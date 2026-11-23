#ifndef BACKWARDREWRITER__HPP__
#define BACKWARDREWRITER__HPP__

#include "Horn.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  class BackwardRewriter
  {
    public:
      BackwardRewriter (ExprFactory &_efac, CHCs& _r, HornRuleExt& _fact,
                        Expr _transBody, int _printLog) :
        m_efac(_efac), ruleManager(_r), fact(_fact),
        transBody(_transBody), printLog(_printLog)
      {
        map<Expr, ExprSet> weights, biases;
        collectCoefficients(weights, biases);
        indexCoefficients(weights);
        indexCoefficients(biases);
        collectTransitions();
      }

      static Expr unprime(Expr e, ExprFactory &efac)
      {
        ExprSet vars;
        filter(e, bind::IsConst(), inserter(vars, vars.begin()));

        ExprMap restoreMap;
        for (auto v : vars)
        {
          string name = lexical_cast<string>(*v);
          if (name.size() > 1 && name.back() == '\'')
            restoreMap[v] = bind::intConst(
              mkTerm<string>(name.substr(0, name.size() - 1), efac));
        }

        return replaceAll(e, restoreMap);
      }

      static bool isFrozenConstSelect(CHCs& r, Expr rel, Expr e)
      {
        if (!isOpX<EQ>(e)) return false;
        Expr sel = e->left(), val = e->right();
        if (isNumericConst(sel)) std::swap(sel, val);
        if (!isOpX<SELECT>(sel) || !isNumericConst(val)) return false;

        Expr arr = sel;
        while (isOpX<SELECT>(arr))
        {
          if (!isNumericConst(arr->right())) return false;
          arr = arr->left();
        }
        int i = getVarIndex(arr, r.invVars[rel]);
        if (i < 0) return false;

        for (auto & hr : r.chcs)
        {
          if (!hr.isInductive || hr.dstRelation != rel) continue;
          ExprSet cnjs;
          getConj(hr.body, cnjs);
          Expr s = hr.srcVars[i], d = hr.dstVars[i];
          if (!cnjs.count(mk<EQ>(d, s)) && !cnjs.count(mk<EQ>(s, d))) return false;
        }
        return true;
      }

      int numberOfLayers()
      {
        Expr counter = ruleManager.invVars[fact.dstRelation][0];
        Expr badStates = ruleManager.chcs[2].body;
        for (int j = 0; j < badStates->arity(); ++j)
        {
          Expr cnj = badStates->arg(j);
          if (cnj->arity() <= 1) continue;
          if (cnj->left() == counter && isNumericConst(cnj->right()))
            return stoi(lexical_cast<string>(cnj->right()));
          if (cnj->right() == counter && isNumericConst(cnj->left()))
            return stoi(lexical_cast<string>(cnj->left()));
        }
        outs() << "Could not read number of layers from file" << endl;
        exit(0);
      }

      Expr classificationProperty()
      {
        Expr counter = ruleManager.invVars[fact.dstRelation][0];
        Expr badStates = ruleManager.chcs[2].body;
        for (int j = 0; j < badStates->arity(); ++j)
        {
          Expr cnj = badStates->arg(j);
          bool mentionsCounter = false;
          for (int i = 0; i < cnj->arity(); ++i)
            if (cnj->arg(i) == counter)
              mentionsCounter = true;

          if (!mentionsCounter) return mk<NEG>(cnj);
        }
        outs() << "Could not read classification property from file" << endl;
        exit(0);
      }

      Expr preimage(Expr property, int layer)
      {
        ExprVector& vars = ruleManager.invVars[fact.dstRelation];
        ExprVector& varsPrime = ruleManager.invVarsPrime[fact.dstRelation];
        if (vars.size() != varsPrime.size())
        {
          outs() << "error: number of primed variables different from number of variables" << endl;
          exit(0);
        }

        ExprMap primeMap;
        for (int i = 0; i < vars.size(); ++i)
          primeMap[vars[i]] = varsPrime[i];
        Expr res = replaceAll(property, primeMap);

        ExprMap counterMap;
        counterMap[vars[0]] = mkMPQ(layer, m_efac);

        ExprMap transitionMap;
        for (auto const& [key, values] : transitions)
        {
          prof::Timer timer("preimage: substituteCoefficients");
          transitionMap[key] = substituteCoefficients(replaceAll(*values.begin(), counterMap));
        }
        {
          prof::Timer timer("preimage: replaceAll transitions");
          res = replaceAll(res, transitionMap);
        }

        prof::Timer timer("preimage: fold");
        ExprMap memo;
        return fold(res, memo);
      }

    private:
      ExprFactory &m_efac;
      CHCs& ruleManager;
      HornRuleExt& fact;
      Expr transBody;
      int printLog;

      map<Expr, ExprSet> transitions;
      unordered_map<string, Expr> coefficients;
      unordered_map<Expr, Expr> lookups;

      void collectCoefficients(map<Expr, ExprSet>& weights, map<Expr, ExprSet>& biases)
      {
        if (fact.body == NULL) return;

        ExprSet cnjs;
        getConj(fact.body, cnjs);
        if (cnjs.empty()) cnjs.insert(fact.body);

        for (auto & lm : cnjs)
        {
          if (lm == NULL || !isOpX<EQ>(lm)) continue;

          Expr var = lm->left(), val = lm->right();
          if (isNumericConst(var)) std::swap(var, val);
          if (!isNumericConst(val) || !isOpX<SELECT>(var)) continue;

          if (isOpX<SELECT>(var->left()))
          {
            weights[var].insert(val);
            if (printLog >= 3) outs() << "W found: " << var << " = " << val << "\n";
          }
          else
          {
            biases[var].insert(val);
            if (printLog >= 3) outs() << "b found: " << var << " = " << val << "\n";
          }
        }
      }

      void indexCoefficients(map<Expr, ExprSet>& coeffs)
      {
        unordered_map<string, ExprSet> grouped;
        for (auto const& [key, values] : coeffs)
          grouped[lexical_cast<string>(unprime(key, m_efac))].insert(*values.begin());

        for (auto const& [key, values] : grouped)
          coefficients.emplace(key, *values.begin());
        lookups.clear();
      }

      void collectTransitions()
      {
        for (int i = 0; i < transBody->arity(); ++i)
        {
          Expr lhs = transBody->arg(i)->left();
          Expr rhs = transBody->arg(i)->right();
          if (isOpX<ITE>(rhs)) transitions[lhs].insert(rhs);
          if (isOpX<ITE>(lhs)) transitions[rhs].insert(lhs);
        }
      }

      Expr lookupCoefficient(Expr s)
      {
        auto it = lookups.find(s);
        if (it != lookups.end()) return it->second;

        auto k = coefficients.find(lexical_cast<string>(s));
        Expr val = (k == coefficients.end()) ? Expr() : k->second;
        lookups[s] = val;
        return val;
      }

      void collectSelects(Expr e, ExprSet& selects, unordered_set<ENode*>& visited)
      {
        if (!visited.insert(&*e).second) return;

        if (isOpX<SELECT>(e))
        {
          selects.insert(e);
          return;
        }

        for (int i = 0; i < e->arity(); ++i)
          collectSelects(e->arg(i), selects, visited);
      }

      Expr substituteCoefficients(Expr e)
      {
        if (coefficients.empty()) return e;

        ExprSet selects;
        unordered_set<ENode*> visited;
        collectSelects(e, selects, visited);

        ExprMap replMap;
        for (auto const& s : selects)
        {
          Expr val = lookupCoefficient(s);
          if (val != NULL) replMap[s] = val;
        }

        Expr res = replaceAll(e, replMap);
        if (printLog >= 2)
          outs() << "substituteCoefficients: selects = " << selects.size()
                 << ", substitutions = " << replMap.size()
                 << ", dag size = " << dagSize(e)
                 << " -> " << dagSize(res) << "\n";

        return res;
      }

      static bool numericValue(Expr e, mpq_class& v)
      {
        if (isOpX<MPQ>(e)) { v = getTerm<mpq_class>(e); return true; }
        if (isOpX<MPZ>(e)) { v = mpq_class(getTerm<mpz_class>(e)); return true; }
        return false;
      }

      Expr mkNum(const mpq_class& v)
      {
        mpq_class r(v);
        r.canonicalize();
        return mkTerm(r, m_efac);
      }

      Expr fold(Expr e, ExprMap& memo)
      {
        auto it = memo.find(e);
        if (it != memo.end()) return it->second;

        Expr res = foldNode(e, memo);
        memo[e] = res;
        return res;
      }

      Expr foldNode(Expr e, ExprMap& memo)
      {
        if (e->arity() == 0 || isOpX<FAPP>(e) || isOpX<SELECT>(e)) return e;
        if (isOpX<ITE>(e))                 return foldIte(e, memo);
        if (isOpX<PLUS>(e))                return foldPlus(e, memo);
        if (isOpX<MULT>(e))                return foldMult(e, memo);
        if (isOpX<UN_MINUS>(e))            return foldUnaryMinus(e, memo);
        if (isOpX<AND>(e) || isOpX<OR>(e)) return foldJunction(e, memo);
        if (isOpX<NEG>(e))                 return foldNeg(e, memo);
        return foldGeneric(e, memo);
      }

      Expr foldUnaryMinus(Expr e, ExprMap& memo)
      {
        mpq_class v;
        Expr s = fold(e->left(), memo);
        return numericValue(s, v) ? mkNum(-v) : mk<UN_MINUS>(s);
      }

      Expr foldNeg(Expr e, ExprMap& memo)
      {
        Expr s = fold(e->left(), memo);
        if (isOpX<TRUE>(s)) return mk<FALSE>(m_efac);
        if (isOpX<FALSE>(s)) return mk<TRUE>(m_efac);
        if (isOpX<NEG>(s)) return s->left();
        return mk<NEG>(s);
      }

      Expr foldIte(Expr e, ExprMap& memo)
      {
        Expr c = fold(e->arg(0), memo);
        if (isOpX<TRUE>(c)) return fold(e->arg(1), memo);
        if (isOpX<FALSE>(c)) return fold(e->arg(2), memo);
        Expr t = fold(e->arg(1), memo);
        Expr f = fold(e->arg(2), memo);
        return (t == f) ? t : mk<ITE>(c, t, f);
      }

      Expr foldPlus(Expr e, ExprMap& memo)
      {
        mpq_class sum = 0, v;
        ExprVector terms;
        for (auto a = e->args_begin(); a != e->args_end(); ++a)
        {
          Expr s = fold(*a, memo);
          if (numericValue(s, v)) sum += v;
          else terms.push_back(s);
        }
        if (sum != 0 || terms.empty()) terms.insert(terms.begin(), mkNum(sum));
        return (terms.size() == 1) ? terms[0] : mknary<PLUS>(terms);
      }

      Expr foldMult(Expr e, ExprMap& memo)
      {
        mpq_class prod = 1, v;
        ExprVector terms;
        for (auto a = e->args_begin(); a != e->args_end(); ++a)
        {
          Expr s = fold(*a, memo);
          if (numericValue(s, v)) prod *= v;
          else terms.push_back(s);
        }
        if (prod == 0) return mkNum(0);
        if (prod != 1 || terms.empty()) terms.insert(terms.begin(), mkNum(prod));
        return (terms.size() == 1) ? terms[0] : mknary<MULT>(terms);
      }

      Expr foldJunction(Expr e, ExprMap& memo)
      {
        bool isAnd = isOpX<AND>(e);
        ExprSet args;
        for (auto a = e->args_begin(); a != e->args_end(); ++a)
        {
          Expr s = fold(*a, memo);
          if (isOpX<TRUE>(s) || isOpX<FALSE>(s))
          {
            if (isOpX<TRUE>(s) == isAnd) continue;
            args.clear();
            args.insert(s);
            break;
          }
          args.insert(s);
        }
        return isAnd ? conjoin(args, m_efac) : disjoin(args, m_efac);
      }

      static bool isComparison(Expr e)
      {
        return isOpX<EQ>(e) || isOpX<NEQ>(e) || isOpX<GEQ>(e) ||
               isOpX<LEQ>(e) || isOpX<GT>(e) || isOpX<LT>(e);
      }

      static bool compare(Expr e, const mpq_class& v, const mpq_class& w)
      {
        if (isOpX<EQ>(e))  return v == w;
        if (isOpX<NEQ>(e)) return v != w;
        if (isOpX<GEQ>(e)) return v >= w;
        if (isOpX<LEQ>(e)) return v <= w;
        if (isOpX<GT>(e))  return v > w;
        if (isOpX<LT>(e))  return v < w;
        
        outs() << "Wrong expression detected" << endl;
        return v < w;
      }

      Expr foldGeneric(Expr e, ExprMap& memo)
      {
        mpq_class v, w;
        ExprVector args;
        for (auto a = e->args_begin(); a != e->args_end(); ++a)
          args.push_back(fold(*a, memo));

        if (args.size() == 2 && numericValue(args[0], v) && numericValue(args[1], w) &&
            isComparison(e))
          return compare(e, v, w) ? mk<TRUE>(m_efac) : mk<FALSE>(m_efac);

        if (isOpX<MINUS>(e) && numericValue(args[0], v))
        {
          bool allNumeric = true;
          for (int i = 1; i < args.size() && allNumeric; i++)
          {
            if (numericValue(args[i], w)) v -= w;
            else allNumeric = false;
          }
          if (allNumeric) return mkNum(v);
        }

        return m_efac.mkNary(e->op(), args.begin(), args.end());
      }
  };
}

#endif
