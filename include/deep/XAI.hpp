#ifndef XAI2__HPP__
#define XAI2__HPP__

#include "RndLearnerV4.hpp"
#include "BackwardRewriter.hpp"
#include <cmath>

// use EGG?
// possibility

using namespace std;
using namespace boost;
namespace ufo
{
  Expr property_to_propagate;
  int number_of_layers;
  bool QE2 = false;
  Expr my_if_condition;
  bool SKIP_CHECKS = true;


  class Xai : public RndLearnerV4
  {
    public:
      Xai (ExprFactory &_e, EZ3 &_z3, CHCs& _r, unsigned _to, int _debug) :
        RndLearnerV4 (_e, _z3, _r, _to, 0, 0, 0, 0,
          0, 0, 0, 0, 0, 0, 0, 0, 0, _debug)
          {} // GF: to clean


    void addToCandidates(int ind, Expr e, int debugMarker)
    {
      prof::Timer timer("addToCandidates");
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
      tribool implied;
      {
        prof::Timer timer("addToCandidates: implies (SMT)");
        implied = u.implies(lms, e);
      }
      if (implied) return;

      candidates[ind].push_back(e);

      if (printLog >= 2)
      {
        outs () << "adding to candidates: " << rel << " / "
                << debugMarker << ": ";
                pprint(e);
      }
    }

    Expr origTransBody;

    void processFact(HornRuleExt& c)
    {
      int ind = getVarIndex(c.dstRelation, decls);
      ExprSet fct;
      Expr fact = replaceAll(c.body, c.dstVars, ruleManager.invVars[c.dstRelation]);
      getConj(fact, fct);

      for (auto f : fct)
      {
        if (!isOpX<EQ>(f)) continue;
        bool frozen;
        {
          prof::Timer timer("processFact: isFrozenConstSelect");
          frozen = SKIP_CHECKS && BackwardRewriter::isFrozenConstSelect(ruleManager, c.dstRelation, f);
        }
        if (frozen)
        {
          prof::Timer timer("processFact: addLemma (frozen)");
          addLemma(ind, sfs[ind].back(), f);
        }
        else
          addToCandidates(ind, f, 48);
      }

      srand(clock());

      unique_ptr<prof::Timer> ctorTimer(new prof::Timer("processFact: BackwardRewriter constructor"));
      BackwardRewriter rewriter(m_efac, ruleManager, c,
        origTransBody ? origTransBody : ruleManager.chcs[1].body, printLog);
      ctorTimer.reset();
      ExprVector& y = ruleManager.invVars[c.dstRelation];

      number_of_layers = rewriter.numberOfLayers();
      Expr property = rewriter.classificationProperty();

      addToCandidates(ind, mk<GEQ>(y[0], mkMPZ(0, m_efac)), 0);
      addToCandidates(ind, mk<LEQ>(y[0], mkMPZ(number_of_layers, m_efac)), 100);

      for (int i = number_of_layers; i >= 0; --i)
      {
        Expr lemma = mk<OR>(mk<NEG>(mk<EQ>(y[0], mkMPZ(i, m_efac))), property);

        if (SKIP_CHECKS)
        {
          prof::Timer timer("processFact: addLemma (layer)");
          addLemma(ind, sfs[ind].back(), lemma);
        }
        else
          addToCandidates(ind, lemma, 1);

        if (i == 0 && SKIP_CHECKS)
          exit(0);

        {
          prof::Timer timer("processFact: preimage, layer " + to_string(i - 1));
          property = rewriter.preimage(property, i - 1);
        }
        prof::count("preimage: dag size of result, layer " + to_string(i - 1), dagSize(property));
      }
    }

    ExprSet iters;

   
    void processTrans(HornRuleExt& c)
    {

      if (QE2)
      {
          Expr property = c.body;
          Expr* LHS = new Expr[property->arity()];
          Expr* RHS = new Expr[property->arity()];
          int size_of_lhs = 0;
          int size_of_rhs = 0;
          
          for (int i=0; i<property->arity(); ++i)
          {
            if (property->arg(i)->left()->arity()==1)
            {
              LHS[i] = property->arg(i)->left();
              size_of_lhs++;
              RHS[i] = property->arg(i)->right();
              size_of_rhs++;

              outs() << LHS[i] << endl;
              outs() << RHS[i] << endl;
            }
          }

     
          property_to_propagate = property_to_propagate->left()->left();

          for (int i=number_of_layers-1; i>=0; --i)
          {
              for (int j=0; j<property_to_propagate->arity(); ++j)
                for (int k=0; k<size_of_lhs; ++k)
                {
                    if (lexical_cast<string>(property_to_propagate->arg(j)->left())==lexical_cast<string>(BackwardRewriter::unprime(LHS[k],m_efac)))
                    {
                   
                    }

                    if (lexical_cast<string>(property_to_propagate->arg(j)->right())==lexical_cast<string>(BackwardRewriter::unprime(LHS[k],m_efac)))
                    {
                      
                    }
                }

              my_if_condition = mk<EQ>(my_if_condition->left(),mkMPZ(i,m_efac));
              Expr last_layer_candidate = mk<OR>(mk<NEG>(my_if_condition),property_to_propagate);
              int ind2 = getVarIndex(c.srcRelation, decls);
              addToCandidates(ind2,last_layer_candidate,55);
            }
        


      
       
          
      }

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
      if (QE2)
      {
        Expr property = c.body;
        property_to_propagate = property->right(); 
        property_to_propagate = mk<NEG>(property_to_propagate);
        number_of_layers = lexical_cast<int>(property->left()->right());
        my_if_condition = mk<EQ>(property->left()->left(),mkMPZ(number_of_layers,m_efac));
        Expr last_layer_candidate = mk<OR>(mk<NEG>(my_if_condition),property_to_propagate);
        int ind2 = getVarIndex(c.srcRelation, decls);
        addToCandidates(ind2,last_layer_candidate,55);
      }


      ExprVector& v0 = ruleManager.invVars[c.srcRelation];
      int ind = getVarIndex(c.srcRelation, decls);

    }

   
    bool transSplit = false;
    void splitTransByLayer(HornRuleExt& c)
    {
      if (transSplit) return;
      int indSrc = getVarIndex(c.srcRelation, decls);
      Expr cnt = c.srcVars[0];

   
      map<Expr, ExprMap> perLayer;
      for (auto & lm : sfs[indSrc].back().learnedExprs)
      {
        if (!isOpX<EQ>(lm)) continue;
        Expr sel = lm->left(), val = lm->right();
        if (isNumericConst(sel)) std::swap(sel, val);
        if (!isOpX<SELECT>(sel) || !isNumericConst(val)) continue;
        Expr lv = sel->right();                      
        if (!isNumericConst(lv)) continue;
        perLayer[lv][mk<SELECT>(sel->left(), cnt)] = val;
      }
      if (perLayer.empty()) return;                   

      ExprVector cases;
      for (auto & a : perLayer)
      {
        Expr bl = replaceAll(c.body, a.second);       
        ExprMap cntRepl;
        cntRepl[cnt] = a.first;
        bl = replaceAll(bl, cntRepl);                
        bl = simplifyBool(simplifyArithm(bl));
        cases.push_back(mk<AND>(mk<EQ>(cnt, a.first), bl));
      }
      origTransBody = c.body;
      c.body = disjoin(cases, m_efac);
      transSplit = true;
    }

    tribool invSyn(int b = 0)
    {

     
      if (b == 2 /* 200 */ /* Change this and report runtimes */) return indeterminate;
      outs () << "\nINV SYN ROUND " << b << "\n";
      outs().flush();
      candidates.clear();


      for(int chc = ruleManager.chcs.size()-1; chc >= 0; chc--)
      {
        auto & c = ruleManager.chcs[chc];
      
        
        string kind = c.isFact ? "fact" : c.isInductive ? "trans" : "query";
        if (b == 0) 
        {
          prof::Timer timer("invSyn: simpEquivClasses (" + kind + ")");
          ExprSet bdy;
          getConj(c.body, bdy);
          ExprVector vars = c.srcVars;
          vars.insert(vars.end(), c.dstVars.begin(), c.dstVars.end());
          c.body = simpEquivClasses(vars, bdy, m_efac);
        }
      
        prof::Timer timer("invSyn: process" + kind);
        if (c.isFact) processFact(c); 
        if (c.isInductive) processTrans(c);
        if (!c.isFact && ! c.isInductive) processQuery(c); 
      }

      for (auto & c : ruleManager.chcs)
        if (c.isInductive)
        {
          prof::Timer timer("invSyn: splitTransByLayer");
          splitTransByLayer(c);
        }

      bool res;
      {
        prof::Timer timer("invSyn: multiHoudini");
        res = multiHoudini(ruleManager.wtoCHCs);
      }
      if (res) assignPrioritiesForLearned();
      bool allChecked = false;
      if (res)
      {
        prof::Timer timer("invSyn: checkAllLemmas");
        allChecked = checkAllLemmas();
      }
      if (res)
      {
        if (allChecked)
        {
         
          return true;
        }
      }
      return invSyn(b + 1);
    }
  };

  inline void learnInvariants5(string smt, unsigned to, int debug, bool quantifier_elimination) // GF: to clean
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3, debug - 2);   
    unique_ptr<prof::Timer> timer(new prof::Timer("learnInvariants5: parse"));
    auto res = ruleManager.parse(smt, 0, 0 /*doArithm*/);
    if (!res) return;
    timer.reset(new prof::Timer("learnInvariants5: initialize"));
    Xai ds(m_efac, z3, ruleManager, to, debug);
    for (auto dcl : ruleManager.decls) ds.initializeDecl(dcl->left());
    timer.reset();

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

