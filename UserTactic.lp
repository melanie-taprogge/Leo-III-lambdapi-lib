/* 
---------------------------------------------------------------------------
Library on User-Defined Tactics for Leo-III Verification
---------------------------------------------------------------------------

This file defines user-defined tactics used in the verification of
Leo-III proofs within Lambdapi. It introduces the abstract `Tactic`
type together with basic tactic combinators and derived strategies
for clausification steps, including:

  • Term simplification
  • Clausification including Skolemization and Quantifier transformations
  • Literal Normalization
---------------------------------------------------------------------------
*/

require open Stdlib.HOL Stdlib.Impred Stdlib.List Leo-III-lambdapi-lib.CNFeq;

/******************************************************************************
 *  Setup for the user defined tactic         
 ******************************************************************************/

 constant symbol Tactic : TYPE;
 symbol tactic : Set;
 rule τ tactic ↪ Tactic;

 constant symbol String : TYPE;
 builtin "String" ≔ String;
 constant symbol string : Set;
 rule τ string ↪ String;
 
 symbol #rewrite : String → String → Π [a], π a → Tactic;
 builtin "rewrite" ≔ #rewrite;
 
 symbol #orelse : Tactic → Tactic → Tactic;
 builtin "orelse" ≔ #orelse;
 notation #orelse infix left 10000;
 
 symbol #refine : String → Tactic;
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
 
 symbol #try : Tactic → Tactic;
 builtin "try" ≔ #try;
 
 symbol #why3 : Tactic;
 builtin "why3" ≔ #why3; 

 symbol #change : Tactic;
 builtin "change" ≔ #change;
 
 // necessary in order to define the tactics
 symbol set0 : Set;
 rule τ set0 ↪ Set; 


/******************************************************************************
 *  Tactic for Leo-III term simplification        
 ******************************************************************************/
  
symbol applyAny : 𝕃 tactic → Tactic;
 rule applyAny ($t0 ⸬ ($t1 ⸬ $tl)) ↪ $t0 #orelse (applyAny ($t1 ⸬ $tl))
 with applyAny ($t0 ⸬ □) ↪ $t0;
 
 symbol listOfAllSimpRules ≔ ((#rewrite "" "" ∨_idem) ⸬ (#rewrite "" "" em_eq_l) ⸬ (#rewrite "" "" em_eq_r) ⸬ (#rewrite "" "" ∨⊤) ⸬ 
     (#rewrite "" "" ⊤∨) ⸬ (#rewrite "" "" ∨⊥) ⸬ (#rewrite "" "" ⊥∨) ⸬ (#rewrite "" "" ∧_idem) ⸬ (#rewrite "" "" ∧_contra_r) ⸬ (#rewrite "" "" ∧_contra_l) ⸬ 
     (#rewrite "" "" ∧⊤) ⸬ (#rewrite "" "" ⊤∧) ⸬ (#rewrite "" "" ∧⊥) ⸬ (#rewrite "" "" ⊥∧) ⸬ (#rewrite "" "" ⇒⊤) ⸬ (#rewrite "" "" ⊥⇒) ⸬ (#rewrite "" "" ⊤⇒) ⸬ 
     (#rewrite "" "" ⇒⊥) ⸬ (#rewrite "" "" ⇒_idem) ⸬ (#rewrite "" "" ⇔⊤) ⸬ (#rewrite "" "" ⊤⇔) ⸬ (#rewrite "" "" ⊥⇔) ⸬ (#rewrite "" "" ⇔⊥) ⸬ 
     (#rewrite "" "" ⇔_idem) ⸬ (#rewrite "" "" ¬⊤) ⸬ (#rewrite "" "" ¬⊥) ⸬ (#rewrite "" "" ¬¬ₑ_eq) ⸬ (#rewrite "" "" =⊤) ⸬ (#rewrite "" "" ⊤=) ⸬ 
     (#rewrite "" "" =⊥) ⸬ (#rewrite "" "" ⊥=) ⸬ (#rewrite "" "" =_idem) ⸬ (#rewrite "" "" ¬=⊥) ⸬ (#rewrite "" "" ¬⊥=) ⸬ (#rewrite "" "" ¬=⊤) ⸬ 
     (#rewrite "" "" ¬⊤=) ⸬ (#rewrite "" "" ¬=_idem) ⸬ (#rewrite "" "" ∀_const) ⸬ (#rewrite "" "" ∃_const) ⸬ (#rewrite "" "" ¬x=_idem) ⸬ (#rewrite "" "" =¬x_idem) ⸬ 
     (#rewrite "" "" polarity_switch) ⸬ (#refine "⊤ᵢ") ⸬ □);
     // the rules and ... are added as Leo omits trivially false literals, we account for this using this rule
 
 symbol applyAllSimplifications ≔ #repeat (applyAny listOfAllSimpRules);


/******************************************************************************
*  Definition of Leo-III clausification tactic        
******************************************************************************/

// Boolean identities

symbol normAsso ≔ #repeat ((#rewrite "" "" ∧_assoc) #orelse (#rewrite "" "" ∨_assoc));

symbol normAsso_∨ ≔ #repeat (#rewrite "" "" ∨_assoc);

symbol normAsso_∧ ≔ #repeat (#rewrite "" "" ∧_assoc);

symbol allCNFids_list ≔ ((#rewrite "" "" deMorgan_∧) ⸬ (#rewrite "" "" deMorgan_∨) ⸬ (#rewrite "" "" ⇒=∨) ⸬ (#rewrite "" "" ¬⇒=∧¬) ⸬ (#and (#rewrite "" "" ∧∨_dist_l) normAsso) ⸬ (#and (#rewrite "" "" ∧∨_dist_r) normAsso) ⸬ (#rewrite "" "" ¬¬ₑ_eq) ⸬ (#rewrite "" "" ∨_assoc) ⸬ (#rewrite "" "" ∧_assoc) ⸬ □);

symbol boolIds ≔ (applyAny allCNFids_list);

symbol onlyBoolIds ≔ #and (#repeat boolIds) #reflexivity;


// skolemisazion

symbol skolemProzess_∃ sk_def : Tactic ≔ (#and (#and (#rewrite "" "" ∃_skolem) #simplify_beta) sk_def);

symbol skolemProzess_∀ sk_def : Tactic ≔ (#and (#and (#rewrite "" "" ∀_skolem) #simplify_beta) sk_def);

symbol skolemProzess sk_def : Tactic ≔ (skolemProzess_∀ sk_def) #orelse (skolemProzess_∃ sk_def);

symbol stepwise_skolem0: 𝕃 tactic → Tactic;
rule stepwise_skolem0 ($sk1 ⸬ ($sk2 ⸬ $sk3)) ↪ #repeat ((#and (skolemProzess $sk1) (stepwise_skolem0 ($sk2 ⸬ $sk3))) #orelse boolIds)
with stepwise_skolem0 ($sk1 ⸬ □) ↪ #and (#repeat ((skolemProzess $sk1) #orelse boolIds)) #reflexivity;

symbol stepwise_skolem: (Tactic → Tactic) → 𝕃 tactic → Tactic;
rule stepwise_skolem $t ($sk1 ⸬ ($sk2 ⸬ $sk3)) ↪ #repeat ((#and ($t $sk1) (stepwise_skolem $t ($sk2 ⸬ $sk3))) #orelse boolIds)
with stepwise_skolem $t ($sk1 ⸬ □) ↪ #and (#repeat (($t $sk1) #orelse boolIds)) #reflexivity;


// handling universal quantification

symbol stepwise_quants: 𝕃 tactic → Tactic;
rule stepwise_quants ($sk1 ⸬ ($sk2 ⸬ $sk3)) ↪ #repeat ((#and $sk1 (stepwise_quants ($sk2 ⸬ $sk3))) #orelse boolIds)
with stepwise_quants ($sk1 ⸬ □) ↪ #and (#repeat ($sk1 #orelse boolIds)) #reflexivity;

symbol move_∀_out_dijs ≔ #repeat (#rewrite  "" "" ∀∨_dist_r) #orelse (#rewrite "" "" ∀∨_dist_l);

symbol move_∀_out (assumeVar: Tactic) ≔ ((#and (#and (((#and (#repeat  (#rewrite "" ".[x in x = _]" ¬¬ₑ_eq)) (#refine "∀_ext _"))) #orelse (#refine "∀_ext _")) (#simplify_beta)) assumeVar) #orelse ((#rewrite "" "" ∀∧_dist_r) #orelse (#rewrite  "" "" ∀∧_dist_l) #orelse (#rewrite  "" "" ∀∨_dist_r) #orelse (#rewrite "" "" ∀∨_dist_l)));

symbol move_¬∃_out (assumeVar: Tactic) ≔ (#and (#rewrite "" "" ¬∃=∀¬) (move_∀_out assumeVar));


/******************************************************************************
 *  Implicit Transformations         
 ******************************************************************************/

// Identification of trivially false literals with ⊥
symbol removeTrivialFalse (pattern: String) ≔ #try ((#rewrite "" pattern ¬=_idem) #orelse (#rewrite "" pattern ¬⊤));

// Normalisation of eqational literals with ⊤ or ⊥ on one side to non-equational ones
symbol normalizeLiteral (pattern: String) ≔ (#rewrite "" pattern =⊤) #orelse (#rewrite "left" pattern =⊤) #orelse (#rewrite "" pattern =⊥) #orelse (#rewrite "left" pattern =⊥); 
