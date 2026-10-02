#ifndef XAI__HPP__
#define XAI__HPP__

#include "RndLearnerV4.hpp"
#include <cmath>

using namespace std;
using namespace boost;
namespace ufo
{
  Expr property_to_propagate;
  int number_of_layers;
  bool QE2 = false;
  Expr my_if_condition;

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

    Expr prime(Expr e, ExprFactory &efac) {
      ExprSet vars;
      
      filter(e, bind::IsConst(), inserter(vars, vars.begin()));

      ExprMap renameMap;
      for (auto v : vars) {
       
        std::ostringstream os;
        os << *v;
        std::string oldName = os.str();
        string newName = oldName + "_p";
        renameMap[v] = bind::intConst(mkTerm<string>(newName, efac));
      }

      return replaceAll(e, renameMap);
    }

    Expr unprime(Expr e, ExprFactory &efac) {
      ExprSet vars;
      filter(e, bind::IsConst(), inserter(vars, vars.begin()));

      ExprMap restoreMap;
      for (auto v : vars) {
        std::ostringstream os;
        os << *v;
        std::string oldName = os.str();
        string name = oldName;

        if (name.size() > 2 && name.substr(name.size() - 2) == "_p") {
            string oldName = name.substr(0, name.size() - 2);
            restoreMap[v] = bind::intConst(mkTerm<string>(oldName, efac));
        }
      }

      return replaceAll(e, restoreMap);
    }

    Expr custom_unprime(Expr e, ExprFactory &efac) {
      ExprSet vars;
      filter(e, bind::IsConst(), inserter(vars, vars.begin()));

      ExprMap restoreMap;
      for (auto v : vars) {
        std::ostringstream os;
        os << *v;
        std::string oldName = os.str();
        string name = oldName;
        if (name.size() > 1 && name.substr(name.size() - 1) == "'") {
            string oldName = name.substr(0, name.size() - 1);
            restoreMap[v] = bind::intConst(mkTerm<string>(oldName, efac));
        }
      }

      return replaceAll(e, restoreMap);
    }

    Expr custom_replace(Expr e, Expr b, ExprFactory &efac) {
      ExprSet vars;
      filter(e, bind::IsConst(), inserter(vars, vars.begin()));

      ExprMap restoreMap;
      for (auto v : vars) {
        std::ostringstream os;
        os << *v;
        std::string oldName = os.str();
        string name = oldName;
        if (name.size() > 1 && name.substr(name.size() - 1) == "'") {
            string oldName = name.substr(0, name.size() - 1);
            restoreMap[v] = bind::intConst(mkTerm<string>(oldName, efac));
        }
      }

      return replaceAll(e, restoreMap);
    }


    void find_initial_point(HornRuleExt& c, map<Expr, ExprSet>& X)
    {
       if (c.body == NULL) return;

      ExprSet bodyConjuncts;
      getConj(c.body, bodyConjuncts);
      if (bodyConjuncts.empty()) bodyConjuncts.insert(c.body);

      for (auto & lm : bodyConjuncts)
      {

        outs() << lm << endl;
        if (lm == NULL || !isOpX<EQ>(lm)) continue;

        Expr var = NULL;
        Expr val = NULL;

       
        if (isNumericConst(lm->left())) {
          val = lm->left();
          var = lm->right();
        } else if (isNumericConst(lm->right())) {
          val = lm->right();
          var = lm->left();
        } else {
          val = lm->left();
          var = lm->right();
         

        }

        if (val == NULL || var == NULL) continue;

        if (!isOpX<SELECT>(var))
        {
            X[var].insert(val);
        }
      }

      // compensate for automatic replacement of values
      for (auto const& [key, values] : X) {
        if (!isNumericConst(*values.begin())) {
            X[key] = X[*values.begin()];
        }
      
      }

    }

    void find_weights_and_biases(HornRuleExt& c, map<Expr, ExprSet>& W, map<Expr, ExprSet>& b)
    {
     
      if (c.body == NULL) return;

      ExprSet bodyConjuncts;
      getConj(c.body, bodyConjuncts);
      if (bodyConjuncts.empty()) bodyConjuncts.insert(c.body);

      for (auto & lm : bodyConjuncts)
      {
        if (lm == NULL || !isOpX<EQ>(lm)) continue;

        Expr var = NULL;
        Expr val = NULL;

       
        if (isNumericConst(lm->left())) {
          val = lm->left();
          var = lm->right();
        } else if (isNumericConst(lm->right())) {
          val = lm->right();
          var = lm->left();
        }

        if (val == NULL || var == NULL) continue;

        if (isOpX<SELECT>(var))
        {
          if (isOpX<SELECT>(var->left()))
          {
            W[var].insert(val);
            if (printLog >= 3) outs() << "W found: " << var << " = " << val << "\n";
          }
          else
          {
            b[var].insert(val);
            if (printLog >= 3)  outs() << "b found: " << var << " = " << val << "\n";
          }
        }
      }
    }

    void find_T(map<Expr, ExprSet>& T)
    {
      for (int i=0; i<ruleManager.chcs[1].body->arity(); ++i)
      {
        Expr left_hs = (Expr) ruleManager.chcs[1].body->arg(i)->left();
        Expr right_hs = (Expr) ruleManager.chcs[1].body->arg(i)->right();
        if (isOpX<ITE>(ruleManager.chcs[1].body->arg(i)->right()))
        {
            T[left_hs].insert(right_hs);
        }
        if (isOpX<ITE>(ruleManager.chcs[1].body->arg(i)->left()))
        {
            T[right_hs].insert(left_hs);
        }
      }
    }

    void get_variable_from_key(ENode* converted_key, Expr& variable)
    {
        if (converted_key->arity()==1)
        {
            Expr E(converted_key);
            variable = E;
        }
        else
        {
          for (int i=0; i<converted_key->arity(); ++i)
            get_variable_from_key(converted_key->arg(i),variable);
        }
    }

    void remap_X_Y(ENode* A, map<Expr, ExprSet>& X, map<Expr,ExprSet>& Y)
    {
        if (A->arity()==0)
        {
          Expr the_A(A);
           for (auto const& [key, values] : X) {

            string the_A_name1 = lexical_cast<std::string>(the_A);
            string the_key_name2 = lexical_cast<std::string>(custom_unprime(key,m_efac));
           
            if (the_A_name1 == the_key_name2)
            {
              if (Y.find(the_A) == Y.end()) {
                Y[the_A].insert(*values.begin());
              }
      
            }
          }
        }
        else
        {
          for (int i=0; i<A->arity(); ++i)
            remap_X_Y(A->arg(i), X, Y);
        }
    }

    Expr substitute_X(ENode* A, map<Expr, ExprSet>& X)
    {

        map<Expr, ExprSet> Y;
        remap_X_Y(A,X,Y);

        Expr old_var_expr(A);
        ExprMap repl_map;
        for (auto const& [key, values]: Y) {
            Expr new_val_expr = *values.begin();
            repl_map[key] = new_val_expr;
        }
        Expr new_tree = replaceAll(old_var_expr, repl_map);
        old_var_expr = new_tree;

        return old_var_expr;


    
        
    }

    void remap_Wb_Wb2(ENode* A, map<Expr, ExprSet>& X, map<Expr,ExprSet>& Y, map<Expr,Expr>& Z)
    {
        if (A->arity()==0)
        {
          Expr the_A(A);

          if (Z.find(the_A)!=Z.end())
            return;

          for (auto const& [key, values] : X) {
            

            Expr E;
            get_variable_from_key(eptr(key),E);
 
            string the_A_name1 = lexical_cast<std::string>(the_A);
            string the_key_name2 = lexical_cast<std::string>(custom_unprime(E,m_efac));
            if (the_A_name1 == the_key_name2)
            {
              Expr key2 = key;
              ExprMap repl_map;
              repl_map[E] = the_A;
              Expr new_tree = replaceAll(key2, repl_map);

              if (Y.find(new_tree) == Y.end()) {
                Y[new_tree].insert(*values.begin());
                Z[the_A] = the_A;
              
              }
            }
          }
        }
        else
        {
          for (int i=0; i<A->arity(); ++i)
            remap_Wb_Wb2(A->arg(i), X, Y, Z);
        }
    }

    void my_custom_replacement(ENode* A, Expr& B, map<Expr, ExprSet>& Y)
    {
      for (auto const& [key, values] : Y) {
        Expr the_A(A);
        string the_A_name1 = lexical_cast<std::string>(the_A);
        string the_key_name2 = lexical_cast<std::string>(custom_unprime(key,m_efac));
        if (the_A_name1 == the_key_name2)
        {

            ExprMap repl_map;
            repl_map[A] = *values.begin();
            ENode* C = eptr(B);
            Expr new_tree = replaceAll(C, repl_map);


            B = new_tree;
          
        }
      }
      
      for (int i=0; i<A->arity(); ++i)
      {
          my_custom_replacement(A->arg(i),B,Y);
      }
    }

    Expr substitute_Wb(ENode* A, map<Expr, ExprSet>& Wb)
    {
        map<Expr, ExprSet> Y;
        map<Expr, Expr> Z;
        remap_Wb_Wb2(A,Wb,Y,Z);

        
        
        Expr old_var_expr(A);
        my_custom_replacement(A,old_var_expr,Y);
        
       
        

        return old_var_expr;

        
    }

    void get_desired_variables_from_key(ENode* converted_key, std::vector<Expr>& desired_variables)
    {
        if (isOpX<NEG>(converted_key))
          get_desired_variables_from_key(converted_key->arg(0), desired_variables);

        if (isOpX<SELECT>(converted_key))
        {
            Expr E(converted_key);
  
            auto it = std::lower_bound(desired_variables.begin(), desired_variables.end(), E,
              [](const Expr& a, const Expr& b) {
                  return boost::lexical_cast<string>(a) < boost::lexical_cast<string>(b);
            });
            
            if (std::find(desired_variables.begin(), desired_variables.end(), E) == desired_variables.end())
              desired_variables.insert(it, E);
        }
        else
        {
          for (int i=0; i<converted_key->arity(); ++i)
            get_desired_variables_from_key(converted_key->arg(i), desired_variables);
        }
    }

    
    void remap_Wb_Wb2_QE(HornRuleExt& c, ENode* A, map<Expr, ExprSet>& X, map<Expr,ExprSet>& Y)
    {
     
      std::vector<Expr> desired_variables;
      get_desired_variables_from_key(A,desired_variables);

      
      for (auto const& [key, values] : X) {
          Expr X_var = key;
          Expr Y_var;
          for (int j=0; j<desired_variables.size(); ++j)
          {
            Y_var = desired_variables[j];
            if (boost::lexical_cast<string>(custom_unprime(X_var,m_efac))==boost::lexical_cast<string>(Y_var))
              Y[desired_variables[j]].insert(*values.begin());
            
          }
      }

  
    
    }

    Expr substitute_Wb_QE(HornRuleExt& c, ENode* A, map<Expr, ExprSet>& Wb)
    {
        map<Expr, ExprSet> Y;
        remap_Wb_Wb2_QE(c,A,Wb,Y);

        
        
        Expr old_var_expr(A);
      

        
        ExprMap repl_map;
        for (auto const& [key, values]: Y) {
            Expr new_val_expr = (Expr) *values.begin();
            repl_map[key] = new_val_expr;
        }

        Expr new_tree = replaceAll(old_var_expr, repl_map);
        old_var_expr = new_tree;
        

       
      
        
      




        
       
        

        return old_var_expr;

        
    }
        

    double double_from_MPQ(Expr& a)
    {
      string aa = boost::lexical_cast<string>(a);
      int division_position = aa.find('/');

      if (division_position == -1)
          return boost::lexical_cast<double>(a);
    


      int num = stoi(aa.substr(0,division_position));
      int den = stoi(aa.substr(division_position+1));
      double quot = ((double) num)/((double) den);

      return quot;
    }

    bool custom_bolean_evaluation(Expr& qq)
    {
      if (qq->arity()>2)
      {
          outs() << "custom_bolean_evaluation: Bad ITE condition" << endl;
          exit(0);
      }


      Expr a(qq->left());
      Expr b(qq->right());
      custom_real_simplification(a);
      custom_real_simplification(b);

      if (a->arity()>1 || b->arity()>1)
      {
          outs() << "custom_bolean_evaluation: Could not simplify ITE condition, probably unsupported operation in custom_real_simplification" << endl;
          exit(0);
      }
      double left_hs = double_from_MPQ(a);
      double right_hs = double_from_MPQ(b);

      if (isOpX<EQ>(qq))
          return (left_hs==right_hs);
      
      if (isOpX<GEQ>(qq))
          return (left_hs>=right_hs);

      if (isOpX<LEQ>(qq))
          return (left_hs<=right_hs);

      if (isOpX<GT>(qq))
          return (left_hs>right_hs);

      if (isOpX<LT>(qq))
          return (left_hs<right_hs);
      
        
       
    }
    
    void custom_real_simplification(Expr& qq)
    {
        if (isOpX<EQ>(qq))
        {
          Expr a(qq->left());
          Expr b(qq->right());
          custom_real_simplification(a);
          custom_real_simplification(b);
          qq = mk<EQ>(a,b);
        }

        if (isOpX<ITE>(qq))
        {
          Expr c(qq->arg(0));
          bool condition = custom_bolean_evaluation(c);

          if (condition)
          {
            Expr d(qq->arg(1));
            custom_real_simplification(d);
            qq = d;
          
          }
          else
          {
            Expr e(qq->arg(2));
            custom_real_simplification(e);
            qq = e;
          }
        }

        if (isOpX<PLUS>(qq))
        {
          double operand = 0;
          for (int i=0; i<qq->arity(); ++i)
          {
            Expr a(qq->arg(i));
            custom_real_simplification(a);
            if (a->arity()>1)
            {
                outs() << "custom_real_simplification: Could not simplify + operation, probably unsupported operation in custom_real_simplification" << endl;
                exit(0);
            }
            operand += double_from_MPQ(a);
          
          }
          qq = mkMPQ(operand,m_efac);
        }

        if (isOpX<MINUS>(qq))
        {
          double operand = 0;
          for (int i=0; i<qq->arity(); ++i)
          {
            Expr a(qq->arg(i));
            custom_real_simplification(a);
            if (a->arity()>1)
            {
                outs() << "custom_real_simplification: Could not simplify - operation, probably unsupported operation in custom_real_simplification" << endl;
                exit(0);
            }
            operand -= double_from_MPQ(a);
          }
          qq = mkMPQ(operand,m_efac);
        }

        if (isOpX<MULT>(qq))
        {
          double operand = 1;
          for (int i=0; i<qq->arity(); ++i)
          {
            Expr a(qq->arg(i));
            custom_real_simplification(a);
            if (a->arity()>1)
            {
                outs() << "custom_real_simplification: Could not simplify * operation, probably unsupported operation in custom_real_simplification" << endl;
                exit(0);
            }
            operand *= double_from_MPQ(a);
          }
          qq = mkMPQ(operand,m_efac);
        }

        if (isOpX<GEQ>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification(a);
          Expr b(qq->arg(1));
          custom_real_simplification(b);

          qq = mk<GEQ>(a,b);
        }

        if (isOpX<LEQ>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification(a);
          Expr b(qq->arg(1));
          custom_real_simplification(b);

          qq = mk<LEQ>(a,b);
        }

        if (isOpX<GT>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification(a);
          Expr b(qq->arg(1));
          custom_real_simplification(b);

          qq = mk<GT>(a,b);
        }

        if (isOpX<LT>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification(a);
          Expr b(qq->arg(1));
          custom_real_simplification(b);

          qq = mk<LT>(a,b);
        }

        if (isOpX<AND>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification(a);
          Expr b(qq->arg(1));
          custom_real_simplification(b);

          qq = mk<AND>(a,b);
        }

        if (isOpX<OR>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification(a);
          Expr b(qq->arg(1));
          custom_real_simplification(b);

          qq = mk<OR>(a,b);
        }

        if (isOpX<NEG>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification(a);

          qq = mk<NEG>(a);
        }


    }

    tribool custom_bolean_evaluation_wp(Expr& qq)
    {
      if (qq->arity()>2)
      {
          outs() << "custom_bolean_evaluation: Bad ITE condition" << endl;
          exit(0);
      }


      Expr a(qq->left());
      Expr b(qq->right());
      custom_real_simplification_wp(a);
      custom_real_simplification_wp(b);

      if (a->arity()>1 || b->arity()>1)
        return indeterminate;

      double left_hs = double_from_MPQ(a);
      double right_hs = double_from_MPQ(b);

      if (isOpX<EQ>(qq))
          return (left_hs==right_hs);
      
      if (isOpX<GEQ>(qq))
          return (left_hs>=right_hs);

      if (isOpX<LEQ>(qq))
          return (left_hs<=right_hs);

      if (isOpX<GT>(qq))
          return (left_hs>right_hs);

      if (isOpX<LT>(qq))
          return (left_hs<right_hs);
      
        
       
    }

    void custom_real_simplification_wp(Expr& qq)
    {
        if (isOpX<EQ>(qq))
        {
          Expr a(qq->left());
          Expr b(qq->right());
          custom_real_simplification_wp(a);
          custom_real_simplification_wp(b);
          qq = mk<EQ>(a,b);
        }

        if (isOpX<ITE>(qq))
        {
          Expr c(qq->arg(0));
          tribool condition = custom_bolean_evaluation_wp(c);

          if (condition==true)
          {
            Expr d(qq->arg(1));
            custom_real_simplification_wp(d);
            qq = d;
          
          }
          if (condition==false)
          {
            Expr e(qq->arg(2));
            custom_real_simplification_wp(e);
            qq = e;
          }
        }

        if (isOpX<PLUS>(qq))
        {
          double operand = 0;
          std::vector<Expr> operand2;
          bool contains_var = false;
          for (int i=0; i<qq->arity(); ++i)
          {
            Expr a(qq->arg(i));
            custom_real_simplification_wp(a);
            
            if (isNumericConst(a))
             operand += double_from_MPQ(a);
            else
            {
             contains_var=true;
             operand2.insert(operand2.begin(),a);
            }
          }
          
          qq = mkMPQ(operand,m_efac);
          if (contains_var)
          {
            if (operand!=0)
            {
            for (int j=0; j<operand2.size(); ++j)
              qq = mk<PLUS>(qq,operand2.at(j));
            }
            else
            {
              qq = operand2.at(0);
              for (int j=1; j<operand2.size(); ++j)
                qq = mk<PLUS>(qq,operand2.at(j));
            }
          }
        }

        if (isOpX<MINUS>(qq))
        {
          double operand = 0;
          std::vector<Expr> operand2;
          bool contains_var = false;
          for (int i=0; i<qq->arity(); ++i)
          {
            Expr a(qq->arg(i));
            custom_real_simplification_wp(a);
            
            if (isNumericConst(a))
             operand -= double_from_MPQ(a);
            else
            {
             contains_var=true;
             operand2.insert(operand2.begin(),a);
            }
          }
          
          qq = mkMPQ(operand,m_efac);
          if (contains_var)
          {
            if (operand!=0)
            {
            for (int j=0; j<operand2.size(); ++j)
              qq = mk<MINUS>(qq,operand2.at(j));
            }
            else
            {
              qq = operand2.at(0);
              for (int j=1; j<operand2.size(); ++j)
                qq = mk<MINUS>(qq,operand2.at(j));
            }
          }
        }

        if (isOpX<MULT>(qq))
        {
          double operand = 1;
          bool contains_var = false;
          bool contains_null = false;
          for (int i=0; i<qq->arity(); ++i)
          {
            Expr a(qq->arg(i));
            custom_real_simplification_wp(a);
            if (isNumericConst(a))
            {
             operand *= double_from_MPQ(a);
             if (double_from_MPQ(a)==0)
              contains_null = true;
            }
            else contains_var = true;
          }
          if (!contains_var)
            qq = mkMPQ(operand,m_efac);
          if (contains_null)
            qq = mkMPQ(0,m_efac);
        }

        if (isOpX<GEQ>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification_wp(a);
          Expr b(qq->arg(1));
          custom_real_simplification_wp(b);

          qq = mk<GEQ>(a,b);
        }

        if (isOpX<LEQ>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification_wp(a);
          Expr b(qq->arg(1));
          custom_real_simplification_wp(b);

          qq = mk<LEQ>(a,b);
        }

        if (isOpX<GT>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification_wp(a);
          Expr b(qq->arg(1));
          custom_real_simplification_wp(b);

          qq = mk<GT>(a,b);
        }

        if (isOpX<LT>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification_wp(a);
          Expr b(qq->arg(1));
          custom_real_simplification_wp(b);

          qq = mk<LT>(a,b);
        }

        if (isOpX<AND>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification_wp(a);
          Expr b(qq->arg(1));
          custom_real_simplification_wp(b);

          if (a!=b)
            qq = mk<AND>(a,b);
          else
            qq = a;
        }

        if (isOpX<OR>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification_wp(a);
          Expr b(qq->arg(1));
          custom_real_simplification_wp(b);

          if (a!=b)
            qq = mk<OR>(a,b);
          else
            qq = a;
        }

        if (isOpX<NEG>(qq))
        {
          Expr a(qq->arg(0));
          custom_real_simplification_wp(a);

          qq = mk<NEG>(a);
        }


    }

    void propagate_forward_a_point(map<Expr, ExprSet>& W, map<Expr, ExprSet>& b, map<Expr, ExprSet>& X, int layer, int max_neurons_per_layer, Expr basic_cnd)
    {
     

      map<Expr, ExprSet> Z;
      for (int i=0; i<ruleManager.chcs[1].body->arity(); ++i)
        if (isOpX<ITE>(ruleManager.chcs[1].body->arg(i)->right()) || isOpX<ITE>(ruleManager.chcs[1].body->arg(i)->left()))
        {
       

          Expr qq = substitute_X(ruleManager.chcs[1].body->arg(i),X);
          ENode* qq2 = eptr(qq);
          qq = substitute_Wb(qq2,W);
          qq2 = eptr(qq);
          qq = substitute_Wb(qq2,b);
          qq2 = eptr(qq);

      
         
           custom_real_simplification(qq);
        


          Z[qq->left()].insert(qq->right());
          
       
        }
       
        Z[((Expr) basic_cnd->arg(0))->left()].insert(mkMPQ(layer+1,m_efac));
        X = Z;
    
    }

    int get_number_of_layers(HornRuleExt& c)
    {
      auto x = ruleManager.invVars[c.dstRelation];
      Expr bad_states = ruleManager.chcs[2].body;
      for (int j=0; j<bad_states->arity(); ++j)
      {
        Expr my_expression = (Expr) bad_states->arg(j);
        if (my_expression->arity()>1)
        {
            if (my_expression->left()==x[0] && isNumericConst(my_expression->right()))
            {
              string number_layers2 = boost::lexical_cast<string>(my_expression->right());
              int number_layers = stoi(number_layers2);
              return number_layers;
            }
            if (my_expression->right()==x[0] && isNumericConst(my_expression->left()))
            {
              string number_layers2 = boost::lexical_cast<string>(my_expression->left());
              int number_layers = stoi(number_layers2);
              return number_layers;
            }
        }
      }

      
      outs() << "Could not read number of layers from file" << endl;
      exit(0);
    }

    Expr get_classification_property(HornRuleExt& c)
    {
      auto x = ruleManager.invVars[c.dstRelation];
      Expr bad_states = ruleManager.chcs[2].body;
      for (int j=0; j<bad_states->arity(); ++j)
      {
        Expr my_expression = (Expr) bad_states->arg(j);
        bool is_there_counter = false;
        for (int i=0; i<my_expression->arity(); ++i)
          if (my_expression->arg(i)==x[0])
            is_there_counter = true;
        
        if (!is_there_counter)
        {
          
          return mk<NEG>(my_expression);
        }
      }
      outs() << "Could not read classification property from file" << endl;
      exit(0);
    }

 

    Expr substitute_T(HornRuleExt& c, ENode* A, map<Expr, ExprSet>& T, int l, map<Expr, ExprSet>& W, map<Expr, ExprSet>& b)
    {
      Expr old_var_expr(A);
      ExprMap repl_map_prime;
      if (ruleManager.invVars[c.dstRelation].size()!=ruleManager.invVarsPrime[c.dstRelation].size())
      {
        outs() << "error: number of primed variables different from number of variables" << endl;
        exit(0);
      }

      for (int i=0; i<ruleManager.invVars[c.dstRelation].size(); ++i)
      {
        Expr aa = (Expr) ruleManager.invVars[c.dstRelation].at(i);
        Expr bb = (Expr) ruleManager.invVarsPrime[c.dstRelation].at(i);
        repl_map_prime[aa] = bb;
      }
    
      Expr new_tree = replaceAll(old_var_expr, repl_map_prime);
      old_var_expr = new_tree;

      ExprMap repl_map;
      for (auto const& [key, values]: T) {
          Expr new_val_expr = *values.begin();
          repl_map[key] = new_val_expr;
      }
      new_tree = replaceAll(old_var_expr, repl_map);
      old_var_expr = new_tree;
    
      ExprMap repl_map_FH_zero;
      repl_map_FH_zero[ruleManager.invVars[c.dstRelation][0]] = mkMPQ(l,m_efac);
      new_tree = replaceAll(old_var_expr, repl_map_FH_zero);
      old_var_expr = new_tree;
     
      old_var_expr = substitute_Wb_QE(c,eptr(old_var_expr),W);
      old_var_expr = substitute_Wb_QE(c,eptr(old_var_expr),b);


      custom_real_simplification_wp(old_var_expr);
     
   
      return old_var_expr;
    }

    void back_propagate_property_once(HornRuleExt& c, Expr& classification, int layer, map<Expr, ExprSet>& W, map<Expr, ExprSet>& b)
    {
        map<Expr, ExprSet> T;
        find_T(T);
        ENode* D = eptr(classification);
        return; // DEBUG MODE
        classification = substitute_T(c,D,T,layer-1,W,b);
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

      srand(clock());

      
      bool QE = true;
      int which_heuristics = -7295;
     // int num_iterations = 10;
      int num_iterations = 100;
      double h_radius = 10;
      int c_radius = 5;
      int INDEX_OF_COUNTER = 0;


      if (QE)
      {
         map<Expr, ExprSet> W, b;
        find_weights_and_biases(c, W, b);

        auto y = ruleManager.invVars[c.dstRelation];

        number_of_layers = get_number_of_layers(c); // get from file
        Expr classification = get_classification_property(c);
       /* Expr backup_candidate = mk<TRUE>(m_efac); */

        Expr my_cnd = mk<GEQ>(y[0],mkMPZ(0,m_efac));
        addToCandidates(ind, my_cnd, 0);
        Expr my_cnd2 = mk<LEQ>(y[0],mkMPZ(number_of_layers,m_efac));
        addToCandidates(ind, my_cnd2, 100);

        for (int i=number_of_layers; i>=0; --i)
        {
          Expr basic_cnd = mk<NEG>(mk<EQ>(y[0],mkMPZ(i,m_efac)));
          Expr new_cnd = mk<OR>(basic_cnd,classification);
          addToCandidates(ind, new_cnd, 1);
         
         /* backup_candidate = mk<AND>(backup_candidate,new_cnd); */
          if (i!=0)
            back_propagate_property_once(c,classification,i,W,b);
        }

        /* addToCandidates(ind, backup_candidate, 2); */
        exit(0);
        return;
      }

      if (which_heuristics==-7295) // abductive explanations -> forward propagation of initial point
      {
          map<Expr, ExprSet> X;
          find_initial_point(c, X);
          map<Expr, ExprSet> W, b;
          find_weights_and_biases(c, W, b);

          int num_layers = 2;
          int max_neurons_per_layer = X.size()-1;
         
          auto y = ruleManager.invVars[c.dstRelation];
          Expr my_cnd = mk<GEQ>(y[0],mkMPZ(0,m_efac));
          addToCandidates(ind, my_cnd, 0);
          Expr my_cnd2 = mk<LEQ>(y[0],mkMPZ(num_layers,m_efac));
          addToCandidates(ind, my_cnd2, 100);

          for (int i=0; i<=num_layers; ++i)
          {
            Expr basic_cnd = mk<NEG>(mk<EQ>(y[0],mkMPZ(i,m_efac)));

            int counter = 0;
            for (auto const& [key, values] : X) {
                Expr new_cnd = mk<EQ>(y[counter],*values.begin());
                ++counter;
                Expr final_cnd = mk<OR>(basic_cnd,new_cnd);
                addToCandidates(ind, final_cnd,50);
            }
            if (i!=num_layers)
              propagate_forward_a_point(W,b,X,i,max_neurons_per_layer,basic_cnd);
          }

          
      }

      if (which_heuristics==-7294)
      {
        Expr cnd;
        Expr cnd2;
        Expr cnd3;
        Expr cnd5;
        Expr cndx;
        Expr cndy;
        Expr cnd0;
        Expr cnd1;
          
        auto x = ruleManager.invVars[c.dstRelation];

        number_of_layers = 2;
        for (int i=0; i<=number_of_layers; ++i)
        {
          Expr basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(i,m_efac)));
          for (int j=0; j<num_iterations; ++j)
            for (auto z: ruleManager.invVars[c.dstRelation])
                if (!isOp<ARRAY_TY>(z->left()->arg(1)))
                {
                  double r1 = (double) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  double r2 = (double) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
           
           
                  
                  cndx = mk<GEQ>(z,mkMPQ(0,m_efac));
                  cnd0 = mk<LEQ>(z,mkMPQ(2,m_efac));
                  cnd1 = mk<LEQ>(z,mkMPZ(3,m_efac));
                  cndy = mk<OR>(basic_cnd,cndx);
                  cnd3 = mk<OR>(basic_cnd,cnd0);
                  cnd5 = mk<OR>(basic_cnd,cnd1);
                 
               
                  addToCandidates(ind, cndy, 56);
                  addToCandidates(ind, cnd3, 56);
                  addToCandidates(ind, cnd5, 56);
                
                 
                }
      }
      }
      
      if (which_heuristics==-7293)
      {
         Expr cnd;
        Expr cnd2;
        Expr cnd3;
        Expr cnd5;
        Expr cndx;
        Expr cndy;
        Expr cnd0;
        Expr cnd1;
          
        auto x = ruleManager.invVars[c.dstRelation];

        number_of_layers = 2;
        for (int i=0; i<=number_of_layers; ++i)
        {
          Expr basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(i,m_efac)));
          for (int j=0; j<num_iterations; ++j)
            for (auto z: ruleManager.invVars[c.dstRelation])
                if (!isOp<ARRAY_TY>(z->left()->arg(1)))
                {
                  double r1 = (double) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  double r2 = (double) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
           
       
                  cnd0 = mk<GEQ>(z,mkMPQ(0,m_efac));
                  cnd1 = mk<LEQ>(z,mkMPZ(2,m_efac));
                  cnd = mk<EQ>(z,mkMPQ(3,m_efac));
                  cnd2 = mk<EQ>(z,mkMPQ(1,m_efac));
                  cndx = mk<EQ>(z,mkMPQ(0,m_efac));
                  cnd3 = mk<OR>(basic_cnd,cnd);
                  cnd5 = mk<OR>(basic_cnd,cnd2);
                  cndy = mk<OR>(basic_cnd,cndx);
              
                  addToCandidates(ind, cnd3, 56);
                  addToCandidates(ind, cnd5, 56);
                  addToCandidates(ind, cndy, 56);
                  addToCandidates(ind, cnd0, 56);
                  addToCandidates(ind, cnd1, 56);
                }
      }
    }
   

      if (which_heuristics==-7291)
      {
        Expr cnd;
        Expr cnd2;
        Expr cnd3;
        Expr cnd5;
        Expr cndx;
        Expr cndy;
          
        auto x = ruleManager.invVars[c.dstRelation];

        number_of_layers = 2;
        for (int i=0; i<=number_of_layers; ++i)
        {
          Expr basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(i,m_efac)));
          for (int j=0; j<num_iterations; ++j)
            for (auto z: ruleManager.invVars[c.dstRelation])
                if (!isOp<ARRAY_TY>(z->left()->arg(1)))
                {
                  double r1 = (double) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  double r2 = (double) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
           
            
                  cnd = mk<LEQ>(z,mkMPQ(r1,m_efac));
                  cnd2 = mk<GEQ>(z,mkMPQ(r2,m_efac));
                  cndx = mk<EQ>(z,mkMPQ(0,m_efac));
                  cnd3 = mk<OR>(basic_cnd,cnd);
                  cnd5 = mk<OR>(basic_cnd,cnd2);
                  cndy =mk<OR>(basic_cnd,cndx);

              
                  addToCandidates(ind, cnd3, 56);
                  addToCandidates(ind, cnd5, 56);
                  addToCandidates(ind, cndy, 56);
                }

            
         
            
              for (auto z: ruleManager.invVars[c.dstRelation])
              for (auto w: ruleManager.invVars[c.dstRelation])
                if (!isOp<ARRAY_TY>(z->left()->arg(1)) && !isOp<ARRAY_TY>(w->left()->arg(1)))
                {
                  double c1 = (double) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  double c2 = (double) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  double c3 = (double) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  
                  
                  cnd = mk<LEQ>(mk<PLUS>(mk<MULT>(z,mkMPQ(c1,m_efac)),mk<MULT>(z,mkMPQ(c2,m_efac))),mkMPQ(c3,m_efac));
                  cnd3 = mk<OR>(basic_cnd,cnd);
                  addToCandidates(ind, cnd3, 58);
                }
            

        }



      }
      

       if (which_heuristics==-6743)
      {
          Expr cnd;
          Expr cnd2;
          Expr cnd3;
          Expr cnd5;
          
          int very_negative = -1000;
          int very_positive = 1000;

          auto x = ruleManager.invVars[c.dstRelation];
          Expr basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(0,m_efac)));
          Expr new_basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(2,m_efac)));

          for (int i=0; i<num_iterations; ++i)
          {
             auto x = ruleManager.invVars[c.dstRelation];
              int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
              int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
              cnd = mk<LEQ>(x[0],mkMPZ(r1,m_efac));
              cnd2 = mk<GEQ>(x[0],mkMPZ(r2,m_efac));
              addToCandidates(ind, cnd, 58);
              addToCandidates(ind, cnd2, 58);
          }

            for (int i=0; i<num_iterations; ++i)
              for (auto z: ruleManager.invVars[c.dstRelation])
                if (!isOp<ARRAY_TY>(z->left()->arg(1)))
                {
                  int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  cnd =  mk<LEQ>(z,mkMPZ(r1,m_efac));
                  cnd2 = mk<GEQ>(z,mkMPZ(r2,m_efac));
                  cnd3 = mk<OR>(new_basic_cnd,cnd);
                  cnd5 = mk<OR>(new_basic_cnd,cnd2);
                  addToCandidates(ind, cnd3, 56);
                  addToCandidates(ind, cnd5, 56);
                }

        
            
      }

      if (which_heuristics==-6742)
      {
          Expr cnd;
          Expr cnd2;
          Expr cnd3;
          Expr cnd5;
    

          auto x = ruleManager.invVars[c.dstRelation];
          Expr basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(0,m_efac)));
          Expr new_basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(2,m_efac)));

            for (int i=0; i<num_iterations; ++i)
              for (auto z: ruleManager.invVars[c.dstRelation])
                if (!isOp<ARRAY_TY>(z->left()->arg(1)))
                {
             
                  cnd =  mk<EQ>(z,mkMPZ(0,m_efac));
                  cnd2 = mk<EQ>(z,mkMPZ(0,m_efac));
             
                  addToCandidates(ind, cnd, 56);
                  addToCandidates(ind, cnd2, 57);
                }
            
      }

      if (which_heuristics==-6741)
      {
          Expr cnd;
          Expr cnd2;
          Expr cnd3;
          Expr cnd5;
          
          int very_negative = -1000;
          int very_positive = 1000;

          auto x = ruleManager.invVars[c.dstRelation];
          Expr basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(0,m_efac)));
          Expr new_basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(2,m_efac)));

            for (int i=0; i<num_iterations; ++i)
              for (auto z: ruleManager.invVars[c.dstRelation])
                if (!isOp<ARRAY_TY>(z->left()->arg(1)))
                {
                  int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  cnd =  mk<LEQ>(z,mkMPZ(r1,m_efac));
                  cnd2 = mk<GEQ>(z,mkMPZ(r2,m_efac));
                  cnd3 = mk<OR>(new_basic_cnd,cnd);
                  cnd5 = mk<OR>(new_basic_cnd,cnd2);
                  addToCandidates(ind, cnd3, 56);
                  addToCandidates(ind, cnd5, 56);
                }
            
      }

     
      if (which_heuristics==-305)
      {
          Expr cnd;
          Expr cnd2;
          Expr cnd3;
          Expr cnd5;

          Expr cnd10;
          Expr cnd11;
          
          int very_negative = -1000;
          int very_positive = 1000;

          auto x = ruleManager.invVars[c.dstRelation];
          Expr basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(0,m_efac)));
          Expr new_basic_cnd = mk<NEG>(mk<EQ>(x[0],mkMPZ(2,m_efac)));
          Expr new_basic_cnd1 = mk<NEG>(mk<EQ>(x[0],mkMPZ(1,m_efac)));

          
            for (auto z: ruleManager.invVars[c.dstRelation])
              if (!isOp<ARRAY_TY>(z->left()->arg(1)))
              {
                
                
                  cnd =  mk<LEQ>(z,mkMPZ(very_positive,m_efac));
                  cnd2 = mk<GEQ>(z,mkMPZ(very_negative,m_efac));
                  
                  cnd3 = mk<OR>(basic_cnd,cnd);
                  cnd5 = mk<OR>(basic_cnd,cnd2);

              
                  addToCandidates(ind, cnd3, 55);
                  addToCandidates(ind, cnd5, 55);

              }

         
            for (int i=0; i<num_iterations; ++i)
              for (auto z: ruleManager.invVars[c.dstRelation])
                if (!isOp<ARRAY_TY>(z->left()->arg(1)))
                {
                  int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  cnd =  mk<LEQ>(z,mkMPZ(r1,m_efac));
                  cnd2 = mk<GEQ>(z,mkMPZ(r2,m_efac));
                  cnd3 = mk<OR>(new_basic_cnd,cnd);
                  cnd5 = mk<OR>(new_basic_cnd,cnd2);
                  cnd10 = mk<OR>(new_basic_cnd1,cnd);
                  cnd11 = mk<OR>(new_basic_cnd1,cnd2);
               
                }
            
         
      }


      if (which_heuristics==-302)
      {
        Expr cnd;
        Expr cnd2;
        Expr cnd3;
        for (int i=0; i<num_iterations; ++i)
          for (auto x: ruleManager.invVars[c.dstRelation])
              if (!isOp<ARRAY_TY>(x->left()->arg(1)))
              {
                
                  int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r3 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  cnd =  mk<LEQ>(x,mkMPZ(r1,m_efac));
                  cnd2 = mk<GEQ>(x,mkMPZ(r2,m_efac));
                  cnd3 = mk<EQ>(x,mkMPZ(r2,m_efac));
                  addToCandidates(ind, cnd, 53);
                  addToCandidates(ind, cnd2, 54);
                  addToCandidates(ind, cnd3, 55);
              }
      }

     if (which_heuristics==-202)
    {
        Expr cnd;
        Expr cnd2;
        auto xf = ruleManager.invVars[c.dstRelation];
        Expr basic_cnd = mk<NEG>(mk<EQ>(xf[0],mkMPZ(0,m_efac)));
        int counter = 0;
          for (auto x: ruleManager.invVars[c.dstRelation])
              if (!isOp<ARRAY_TY>(x->left()->arg(1)))
              {
                  int r3 = (int) (10*((double) rand()/RAND_MAX));
                  basic_cnd = mk<NEG>(mk<EQ>(xf[0],mkMPZ(r3,m_efac)));
                  if (counter == 0) {
                    int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                    int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);

                    cnd =  mk<LEQ>(x,mkMPZ(r1,m_efac));
                    cnd2 = mk<GEQ>(x,mkMPZ(r2,m_efac));
                    addToCandidates(ind, cnd, 53);
                    addToCandidates(ind, cnd2, 54);
                  }
                  else {
                        int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                        int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);

                        cnd =  mk<LEQ>(x,mkMPZ(r1,m_efac));
                        cnd2 = mk<GEQ>(x,mkMPZ(r2,m_efac));
                        cnd = mk<OR>(basic_cnd,cnd);
                        cnd2 = mk<OR>(basic_cnd,cnd2);
                        addToCandidates(ind, cnd, 53);
                        addToCandidates(ind, cnd2, 54);
                  }
                  
                  counter += 1;
              }
    }

     

      
      if (which_heuristics == -105)
      {
         
          map<Expr, ExprSet> W, b;
          find_weights_and_biases(c, W, b);

          int NUM_SIMULATIONS = 5;
          int number_layers = 2;
          int which_class = 0;
          
          auto& invVars = ruleManager.invVars[c.dstRelation];
          if (invVars.size() == 0) return;

          for (int i = 0; i < NUM_SIMULATIONS; ++i)
          {

              // OUTER LAYER
              Expr basic_formula = mk<TRUE>(m_efac);
              for (auto x : invVars) {
                  if (x != invVars[which_class]) {
                      basic_formula = mk<AND>(basic_formula, mk<GEQ>(invVars[which_class], x));
                  }
              }
              
            
              for (int current = number_layers; current >= 0; --current)
              {
                  ExprMap substMap;
                  for (size_t j = 0; j < invVars.size(); ++j)
                  {
                      if (isOpX<ARRAY_TY>(invVars[j])) {
                        Expr weighted_sum = mkMPZ(0, m_efac);
                        for (auto const& [key, values] : W) {
                            if (!values.empty()) {
                                Expr weight = *values.begin();
                                weighted_sum = mk<PLUS>(weighted_sum, mk<MULT>(weight, invVars[j]));
                            }
                        }
                       
                        substMap[prime(invVars[j],m_efac)] = weighted_sum;
                    }
                  }
                 
                  basic_formula = prime(basic_formula,m_efac);
                  basic_formula = replaceAll(basic_formula, substMap);
                 
                  basic_formula = unprime(basic_formula,m_efac);
                
                  if (!isOpX<TRUE>(basic_formula) && !isOpX<FALSE>(basic_formula)) {
                    
                      addToCandidates(ind, basic_formula, 10400 + current);
                  }
              }
          }
      }


      if (which_heuristics == -104)
      {
          map<Expr, ExprSet> W, b;
          find_weights_and_biases(c, W, b);

          if (!W.empty() || !b.empty()) {
             
              ExprSet varsToEliminate;
              filter(c.body, bind::IsConst(), inserter(varsToEliminate, varsToEliminate.begin()));
              
             
              for (auto v : ruleManager.invVars[c.dstRelation]) {
                  varsToEliminate.erase(v);
              }

              for (auto const& [var_w, values_w] : W) {
                  for (auto val_w : values_w) {
                      for (auto const& [var_b, values_b] : b) {
                          for (auto val_b : values_b) {
                              
                            
                              Expr term = mk<PLUS>(mk<MULT>(val_w, var_w), val_b);
                              Expr query = mk<GEQ>(term, mkMPZ(0, m_efac));

                           
                              Expr qed = ufo::eliminateQuantifiers(query, varsToEliminate);

                              if (qed != NULL && !isOpX<TRUE>(qed) && !isOpX<FALSE>(qed)) {
                                 
                                  addToCandidates(ind, qed, 104);
                              }
                          }
                      }
                  }
              }
          }
      }


      
 
 

 
      if (which_heuristics==-102)
      {
        Expr cnd;
        Expr cnd2;
        for (int i=0; i<num_iterations; ++i)
          for (auto x: ruleManager.invVars[c.dstRelation])
              if (!isOp<ARRAY_TY>(x->left()->arg(1)))
              {
                
                  int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);

                  cnd =  mk<LEQ>(x,mkMPZ(r1,m_efac));
                  cnd2 = mk<GEQ>(x,mkMPZ(r2,m_efac));
                  addToCandidates(ind, cnd, 53);
                  addToCandidates(ind, cnd2, 54);
              }
      }

      if (which_heuristics==-2)
      {
        Expr cnd;
        Expr cnd2;
        int counter = 0;
        for (int i=0; i<num_iterations; ++i)
        {
          for (auto x: ruleManager.invVars[c.dstRelation])
          {
            if (!isOp<ARRAY_TY>(x->left()->arg(1)) && counter>0)
            {
              int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
              int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
              int r3 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
              int r4 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
              cnd = mk<GEQ>(mk<MULT>(x,mkMPZ(r1,m_efac)),mkMPZ(r2,m_efac));
              cnd2 = mk<LEQ>(mk<MULT>(x,mkMPZ(r3,m_efac)),mkMPZ(r4,m_efac));
              addToCandidates(ind, cnd, 51);
              addToCandidates(ind, cnd2, 52);
            }
            ++counter;
          }
        }
      }

      if (which_heuristics==-1)
      {
        Expr cnd;
        Expr cnd2;
        int counter = 0;
        for (auto x: ruleManager.invVars[c.dstRelation])
        {
          if (!isOp<ARRAY_TY>(x->left()->arg(1)) && counter>0)
          {
            cnd = mk<EQ>(x,mkMPZ(0,m_efac));
        
            addToCandidates(ind, cnd, 51);
     
          }
          ++counter;
        }
      }

      if (which_heuristics==1)
      {
       
        h_radius = 100*h_radius;
        Expr cnd;
        Expr cnd2;

        for (int i=0; i<num_iterations; ++i)
          for (auto x: ruleManager.invVars[c.dstRelation])
            if (!isOp<ARRAY_TY>(x->left()->arg(1)))
            {
                int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                cnd = mk<LEQ>(x,mkMPZ(r1,m_efac));
                cnd2 = mk<GEQ>(x,mkMPZ(r2,m_efac));
                addToCandidates(ind, cnd, 49);
                addToCandidates(ind, cnd2, 50);
            }
      }

      if (which_heuristics==2)
      {
       
       
        Expr cnd;
        Expr cnd2;
        for (int i=0; i<num_iterations; ++i)
          for (auto x: ruleManager.invVars[c.dstRelation])
            for (auto y: ruleManager.invVars[c.dstRelation])
              if (!isOp<ARRAY_TY>(x->left()->arg(1)) && !isOp<ARRAY_TY>(y->left()->arg(1)))
              {
                  int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  cnd = mk<LEQ>(mk<PLUS>(x,y),mkMPZ(r1,m_efac));
                  cnd2 = mk<GEQ>(mk<PLUS>(x,y),mkMPZ(r2,m_efac));
                  addToCandidates(ind, cnd, 51);
                  addToCandidates(ind, cnd2, 52);
              }
      }

      if (which_heuristics==3)
      {

       
        
        Expr cnd;
        Expr cnd2;
        for (int i=0; i<num_iterations; ++i)
          for (auto x: ruleManager.invVars[c.dstRelation])
            for (auto y: ruleManager.invVars[c.dstRelation])
              if (!isOp<ARRAY_TY>(x->left()->arg(1)) && !isOp<ARRAY_TY>(y->left()->arg(1)))
              {
                  int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r3 = (int) (2*c_radius*((double) rand()/RAND_MAX) - c_radius);
                  int r4 = (int) (2*c_radius*((double) rand()/RAND_MAX) - c_radius);
                  int r5 = (int) (2*c_radius*((double) rand()/RAND_MAX) - c_radius);
                  int r6 = (int) (2*c_radius*((double) rand()/RAND_MAX) - c_radius);
                  
                  cnd = mk<LEQ>(mk<PLUS>(mk<MULT>(x,mkMPZ(r3,m_efac)),mk<MULT>(y,mkMPZ(r4,m_efac))),mkMPZ(r1,m_efac));
                  cnd2 = mk<GEQ>(mk<PLUS>(mk<MULT>(x,mkMPZ(r5,m_efac)),mk<MULT>(y,mkMPZ(r6,m_efac))),mkMPZ(r2,m_efac));
                  addToCandidates(ind, cnd, 53);
                  addToCandidates(ind, cnd2, 54);
              }
      }

      if (which_heuristics==1004)
      {
          int basic_directon_x = 1;
          int basic_directon_y = 1;
          Expr cnd;
          Expr cnd2;
          for (int i=0; i<num_iterations; ++i)
          {
            
          }
      }

      if (which_heuristics==14)
      {
          int counter = 0;
          Expr basic_cnd;
          for (auto x: ruleManager.invVars[c.dstRelation])
              if (counter==0)
              {
                  basic_cnd = mk<NEG>(mk<EQ>(x,mkMPZ(3,m_efac)));
                  counter += 1;
              }

          h_radius = 100*h_radius;
          Expr cnd;
          Expr cnd2;

          for (int i=0; i<num_iterations; ++i)
            for (auto x: ruleManager.invVars[c.dstRelation])
              if (!isOp<ARRAY_TY>(x->left()->arg(1)))
              {
                  int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                  cnd = mk<OR>(basic_cnd,mk<LEQ>(x,mkMPZ(r1,m_efac)));
                  cnd2 = mk<OR>(basic_cnd,mk<GEQ>(x,mkMPZ(r2,m_efac)));
                  addToCandidates(ind, cnd, 49);
                  addToCandidates(ind, cnd2, 50);
              }
      }

      
      if (which_heuristics==15)
      {
          int counter = 0;
          Expr basic_cnd;
          for (auto x: ruleManager.invVars[c.dstRelation])
              if (counter==0)
              {
                  basic_cnd = mk<NEG>(mk<EQ>(x,mkMPZ(0,m_efac)));
                  counter += 1;
              }

          Expr cnd;
          Expr cnd2;

          for (int i=0; i<num_iterations; ++i)
            for (auto x: ruleManager.invVars[c.dstRelation])
              for (auto y: ruleManager.invVars[c.dstRelation])
                if (!isOp<ARRAY_TY>(x->left()->arg(1)) && !isOp<ARRAY_TY>(y->left()->arg(1)))
                {
                    int r1 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                    int r2 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                    int r3 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                    int r4 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                    int r5 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                    int r6 = (int) (2*h_radius*((double) rand()/RAND_MAX) - h_radius);
                    cnd = mk<OR>(basic_cnd,mk<LEQ>(mk<PLUS>(mk<MULT>(x,mkMPZ(r1,m_efac)),mk<MULT>(y,mkMPZ(r2,m_efac))),mkMPZ(r3,m_efac)));
                    cnd2 = mk<OR>(basic_cnd,mk<GEQ>(mk<PLUS>(mk<MULT>(x,mkMPZ(r4,m_efac)),mk<MULT>(y,mkMPZ(r5,m_efac))),mkMPZ(r6,m_efac)));
                    addToCandidates(ind, cnd, 49);
                    addToCandidates(ind, cnd2, 50);
                }
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
                    if (lexical_cast<string>(property_to_propagate->arg(j)->left())==lexical_cast<string>(custom_unprime(LHS[k],m_efac)))
                    {
                     
                    }

                    if (lexical_cast<string>(property_to_propagate->arg(j)->right())==lexical_cast<string>(custom_unprime(LHS[k],m_efac)))
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
          //  cout << var << " = " << val << endl;
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

    tribool invSyn(int b = 0)
    {

    
      if (b == 200 /* Change this and report runtimes */) return indeterminate;
      outs () << "\nINV SYN ROUND " << b << "\n";
      outs().flush();
      candidates.clear();


      for(int chc = ruleManager.chcs.size()-1; chc >= 0; chc--)
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

       
        if (c.isFact) processFact(c); // <- changed
        if (c.isInductive) processTrans(c);
        if (!c.isFact && ! c.isInductive) processQuery(c);
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

  inline void learnInvariants5(string smt, unsigned to, int debug, bool quantifier_elimination) // GF: to clean
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

