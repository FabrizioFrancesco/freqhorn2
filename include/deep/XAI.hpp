#ifndef XAI__HPP__
#define XAI__HPP__

#include "RndLearnerV4.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class Xai : public RndLearnerV4
  {
    public:
      Xai (ExprFactory &_e, EZ3 &_z3, CHCs& _r, unsigned _to, int _debug) :
        RndLearnerV4 (_e, _z3, _r, _to, 0, 0, 0, 0,
          0, 0, 0, 0, 0, 0, 0, 0, 0, _debug)
          {} // GF: to clean


    void addToCandidates(int ind, Expr e, int debugMarker)
    {
      Expr rel = decls[ind];
      if (!hasOnlyVars(e, ruleManager.invVars[rel])) return;

      if (!containsOp<FAPP>(e)) return;

      e = simplifyBool(simplifyArithm(e));
      if (find(candidates[ind].begin(), candidates[ind].end(), e) !=
               candidates[ind].end()) return;

      if (isOpX<EQ>(e)) // symmetric case
      {
        if (find(candidates[ind].begin(), candidates[ind].end(),
            mk<EQ>(e->right(), e->left())) !=
                 candidates[ind].end()) return;
      }

      Expr lms = conjoin(sfs[ind].back().learnedExprs, m_efac);
      if (u.implies(lms, e)) return;

      candidates[ind].push_back(e);

      if (printLog >= 2)
      {
        outs () << "adding to candidates: " << rel << " / "
                << debugMarker << ": ";
                pprint(e);
      }
    }

    void processFact(HornRuleExt& c)
    {
      int ind = getVarIndex(c.dstRelation, decls);
      ExprSet fct;
      Expr fact = replaceAll(c.body, c.dstVars, ruleManager.invVars[c.dstRelation]);
      getConj(fact, fct);
      for (auto f : fct)
      {
        if (isOpX<EQ>(f))
        {
          addToCandidates(ind, f, 48);
        }
      }
    }

    ExprSet iters;

    void processTrans(HornRuleExt& c)
    {
      int indSrc = getVarIndex(c.srcRelation, decls);
      int indDst = getVarIndex(c.dstRelation, decls);

      ExprSet coeffs;
      map <Expr, ExprSet> values;
      Expr itbl = NULL, itbu = NULL;

      for (auto & lm : sfs[indSrc].back().learnedExprs)
      {
        if (isOpX<EQ>(lm))
        {
          Expr var = NULL;
          Expr val = NULL;
          if (isNumericConst(lm->left()))
          {
            val = lm->left();
            var = lm->right();
          }
          if (isNumericConst(lm->right()))
          {
            val = lm->right();
            var = lm->left();
          }
          if (val == NULL) continue;

          if (isOpX<SELECT>(var) && isOpX<SELECT>(var->left()))
          {
            coeffs.insert(var->left());
            values[var->left()].insert(val);
            iters.insert(var->right());
          }
        }
        if (isOpX<LEQ>(lm))
        {
          if (lm->left() == c.srcVars[0]) itbu = lm->right();
        }
        if (isOpX<GEQ>(lm))
        {
          if (lm->left() == c.srcVars[0]) itbl = lm->right();
        }
      }

      if (!iters.empty())
      {
        ExprVector its;
        its.insert(its.end(), iters.begin(), iters.end());
        std::sort(its.begin(), its.end(), [](Expr& x, Expr& y) {return x < y;});
        addToCandidates(indSrc, mk<GEQ>(c.srcVars[0], its.front()), 1);
        addToCandidates(indSrc, mk<LEQ>(c.srcVars[0],
          mk<PLUS>(mkMPZ(1, m_efac), its.back())), 2);
      }

      if (itbl != NULL && itbu != NULL)
      {
        int sz = dagSize(c.body);
        ExprMap repl;
        for (auto & a : values)
          if (a.second.size() == 1)
            repl[mk<SELECT>(a.first, c.srcVars[0])] = *a.second.begin();
          c.body = replaceAll(c.body, repl);
          c.body = simplifyArithm(c.body);

        if (printLog >= 2)
          outs () << "simplified: " << sz << " -> " << dagSize(c.body) << "\n";
      }
    }

    void processQuery(HornRuleExt& c)
    {
      ExprVector& v0 = ruleManager.invVars[c.srcRelation];
      int ind = getVarIndex(c.srcRelation, decls);
      addToCandidates(ind, mkNeg(c.body), 55);
    }

    tribool invSyn(int b = 0)
    {
      if (b == 3 /* hardcoded threshold */) return indeterminate;
      outs () << "\nINV SYN ROUND " << b << "\n";
      outs().flush();
      candidates.clear();

      for(int chc = 0; chc < ruleManager.chcs.size(); chc++)
      {
        auto & c = ruleManager.chcs[chc];

        if (b == 0) // preprocess
        {
          ExprSet bdy;
          getConj(c.body, bdy);
          ExprVector vars = c.srcVars;
          vars.insert(vars.end(), c.dstVars.begin(), c.dstVars.end());
          c.body = simpEquivClasses(vars, bdy, m_efac);
        }

        if (c.isFact && b == 0) processFact(c);
        if (c.isInductive) processTrans(c);
      }

      auto res = multiHoudini(ruleManager.wtoCHCs);
      if (res) assignPrioritiesForLearned();
      if (res)
      {
        if (checkAllLemmas())
        {
          return true;
        }
      }
      return invSyn(b + 1);
    }
  };

  inline void learnInvariants5(string smt, unsigned to, int debug) // GF: to clean
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3, debug - 2);
    auto res = ruleManager.parse(smt, 0, 0 /*doArithm*/);
    if (!res) return;

    Xai ds(m_efac, z3, ruleManager, to, debug);

    for (auto dcl : ruleManager.decls) ds.initializeDecl(dcl->left());

    if (ds.invSyn())
    {
      ds.printSolution(false);
      errs() << "sat\n";
    }
    else
      errs() << "unknown\n";
  }
}

#endif
