require open Stdlib.Set Stdlib.Prop Stdlib.PropExt Stdlib.List;

/******************************************************************************
 *  Setup for the user defined tactic         
 ******************************************************************************/

 constant symbol Tactic : TYPE;
 symbol tactic : Set;
 rule τ tactic ↪ Tactic;
 
 symbol #rewrite : Π [a], π a → τ tactic;
 builtin "rewrite" ≔ #rewrite;

 symbol #rewrite_left [a] : π a → Tactic;
 builtin "rewrite left" ≔ #rewrite_left;
 
 constant symbol String : TYPE;
 builtin "String" ≔ String;
 
 symbol #orelse : Tactic → Tactic → Tactic;
 builtin "orelse" ≔ #orelse;
 notation #orelse infix left 10000;
 
 symbol #refine : Π [a], π a → Tactic;
 builtin "refine" ≔ #refine;
 
 symbol #repeat : Tactic → Tactic;
 builtin "repeat" ≔ #repeat;
 
 symbol #fail : Tactic;
 builtin "fail" ≔ #fail;
 
 symbol #admit : Tactic;
 builtin "admit" ≔ #admit;
 
 symbol #and : Tactic → Tactic → Tactic;
 builtin "and" ≔ #and;
 
 symbol #apply : Π [a], π a → Tactic;
 builtin "apply" ≔ #apply;
 
 symbol #assume : String → Tactic;
 builtin "assume" ≔ #assume;
 
 symbol #generalize : Π [a], π a → Tactic;
 builtin "generalize" ≔ #generalize;
 
 symbol #have : String → Π [a], π a → Tactic;
 builtin "have" ≔ #have; 
 
 symbol #induction : Tactic;
 builtin "induction" ≔ #induction; 
 
 symbol #remove : Π [a], π a → Tactic;
 builtin "remove" ≔ #remove;
 
 symbol #reflexivity : Tactic;
 builtin "reflexivity" ≔ #reflexivity;
 
 symbol #set : String → Π [a], π a → Tactic;
 builtin "set" ≔ #set;
 
 symbol #simplify : Tactic;
 builtin "simplify" ≔ #simplify;

 symbol #simplify_beta : Tactic;
 builtin "simplify rule off" ≔ #simplify_beta;
 
 symbol #solve : Tactic;
 builtin "solve" ≔ #solve;
 
 symbol #symmetry : Tactic;
 builtin "symmetry" ≔ #symmetry;
 
 symbol #try : Tactic;
 builtin "try" ≔ #try;
 
 symbol #why3 : Tactic;
 builtin "why3" ≔ #why3; 

 
 // necessary in order to define the tactics
 protected symbol set0 : Set;
 rule τ set0 ↪ Set;
 
 
/******************************************************************************
*  Definition of Leo-III simplification tactic        
******************************************************************************/
 
 symbol applyAny : 𝕃 tactic → Tactic;
 rule applyAny ($t0 ⸬ $tl) ↪ $t0 #orelse (applyAny $tl)
 with applyAny □ ↪ #fail;
 
 symbol listOfAllSimpRules ≔ ((#rewrite ∨_idem) ⸬ (#rewrite em_eq_l) ⸬ (#rewrite em_eq_r) ⸬ (#rewrite ∨⊤) ⸬ 
     (#rewrite ⊤∨) ⸬ (#rewrite ∨⊥) ⸬ (#rewrite ⊥∨) ⸬ (#rewrite ∧_idem) ⸬ (#rewrite ∧_contra_r) ⸬ (#rewrite ∧_contra_l) ⸬ 
     (#rewrite ∧⊤) ⸬ (#rewrite ⊤∧) ⸬ (#rewrite ∧⊥) ⸬ (#rewrite ⊥∧) ⸬ (#rewrite ⇒⊤) ⸬ (#rewrite ⊥⇒) ⸬ (#rewrite ⊤⇒) ⸬ 
     (#rewrite ⇒⊥) ⸬ (#rewrite ⇒_idem) ⸬ (#rewrite ⇔⊤) ⸬ (#rewrite ⊤⇔) ⸬ (#rewrite ⊥⇔) ⸬ (#rewrite ⇔⊥) ⸬ 
     (#rewrite ⇔_idem) ⸬ (#rewrite ¬⊤) ⸬ (#rewrite ¬⊥) ⸬ (#rewrite ¬¬ₑ_eq) ⸬ (#rewrite =⊤) ⸬ (#rewrite ⊤=) ⸬ 
     (#rewrite =⊥) ⸬ (#rewrite ⊥=) ⸬ (#rewrite =_idem) ⸬ (#rewrite ¬=⊥) ⸬ (#rewrite ¬⊥=) ⸬ (#rewrite ¬=⊤) ⸬ 
     (#rewrite ¬⊤=) ⸬ (#rewrite ¬=_idem) ⸬ (#rewrite ∀_const) ⸬ (#rewrite ∃_const) ⸬ (#rewrite polarity_switch) ⸬ (#refine ⊤ᵢ) ⸬ □);
 
 symbol applyAllSimplifications ≔ #repeat (applyAny listOfAllSimpRules);


/******************************************************************************
*  Definition of Leo-III clausification tactic        
******************************************************************************/

symbol normAsso ≔ #repeat ((#rewrite ∧_assoc) #orelse (#rewrite ∨_assoc));

symbol allCNFids_list ≔ ((#rewrite deMorgan_∧) ⸬ (#rewrite deMorgan_∨) ⸬ (#rewrite ⇒=∨) ⸬ (#rewrite ¬⇒=∧¬) ⸬ (#and (#rewrite ∧∨_dist_l) normAsso) ⸬ (#and (#rewrite ∧∨_dist_r) normAsso) ⸬ (#rewrite ¬¬ₑ_eq) ⸬ □);

symbol allCNFids_app ≔ #and (#and (#repeat (applyAny allCNFids_list)) normAsso) #reflexivity;