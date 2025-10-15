require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.FunExt Stdlib.PropExt Stdlib.Nat Stdlib.Bool Stdlib.List Leo-III-lambdapi-lib.Epsilon Leo-III-lambdapi-lib.CNFeq;

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
 protected symbol set0 : Set;
 rule τ set0 ↪ Set;


 /******************************************************************************
 *  Setup for the user defined tactic         
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

symbol normAsso ≔ #repeat ((#rewrite "" "" ∧_assoc) #orelse (#rewrite "" "" ∨_assoc));

symbol normAsso_∨ ≔ #repeat (#rewrite "" "" ∨_assoc);

symbol normAsso_∧ ≔ #repeat (#rewrite "" "" ∧_assoc);

symbol allCNFids_list ≔ ((#rewrite "" "" deMorgan_∧) ⸬ (#rewrite "" "" deMorgan_∨) ⸬ (#rewrite "" "" ⇒=∨) ⸬ (#rewrite "" "" ¬⇒=∧¬) ⸬ (#and (#rewrite "" "" ∧∨_dist_l) normAsso) ⸬ (#and (#rewrite "" "" ∧∨_dist_r) normAsso) ⸬ (#rewrite "" "" ¬¬ₑ_eq) ⸬ (#rewrite "" "" ∨_assoc) ⸬ (#rewrite "" "" ∧_assoc) ⸬ □);

symbol boolIds ≔ (applyAny allCNFids_list);

symbol tryVars: 𝕃 string → Tactic; 
rule tryVars ($v0 ⸬ ($v1 ⸬ $vs)) ↪ (#assume $v0) #orelse (tryVars ($v1 ⸬ $vs))
with tryVars ($v0 ⸬ □) ↪ (#assume $v0);

symbol move_∀_out (varList: 𝕃 string) ≔ #repeat (((#rewrite "" "" ∀∧_dist_r) #orelse (#rewrite  "" "" ∀∧_dist_l) #orelse (#rewrite  "" "" ∀∨_dist_r) #orelse (#rewrite "" "" ∀∨_dist_l)) #orelse (#and (#and (#refine "∀_ext _ _ _") (#simplify_beta))) (tryVars varList));

symbol move_¬∃_out (varList: 𝕃 string) ≔ (#and (#rewrite "" "" ¬∃=∀¬) (move_∀_out varList));

symbol generalizeQuant (varList: 𝕃 string) ≔ (move_∀_out varList) #orelse (move_¬∃_out varList);

symbol skolemProzess_∃ sk_def : Tactic ≔ (#and (#and (#rewrite "" "" ∃_skolem) #simplify_beta) sk_def);

symbol skolemProzess_∀ sk_def : Tactic ≔ (#and (#and (#rewrite "" "" ∀_skolem) #simplify_beta) sk_def);

symbol skolemProzess sk_def : Tactic ≔ (skolemProzess_∀ sk_def) #orelse (skolemProzess_∃ sk_def);

symbol stepwise_quants: 𝕃 tactic → Tactic;
rule stepwise_quants ($sk1 ⸬ ($sk2 ⸬ $sk3)) ↪ #repeat ((#and $sk1 (stepwise_quants ($sk2 ⸬ $sk3))) #orelse boolIds)
with stepwise_quants ($sk1 ⸬ □) ↪ #and (#repeat ($sk1 #orelse boolIds)) #reflexivity;

symbol move_∀_out2 (assumeVar: Tactic) ≔ ((#and (#and (((#and (#repeat  (#rewrite "" ".[x in x = _]" ¬¬ₑ_eq)) (#refine "∀_ext _"))) #orelse (#refine "∀_ext _")) (#simplify_beta)) assumeVar) #orelse ((#rewrite "" "" ∀∧_dist_r) #orelse (#rewrite  "" "" ∀∧_dist_l) #orelse (#rewrite  "" "" ∀∨_dist_r) #orelse (#rewrite "" "" ∀∨_dist_l)));
symbol move_¬∃_out2 (assumeVar: Tactic) ≔ (#and (#rewrite "" "" ¬∃=∀¬) (move_∀_out2 assumeVar));

symbol singleStepQuant: Tactic → Tactic;
rule singleStepQuant $t ↪ #repeat ($t #orelse boolIds);

symbol lastStepQuant: Tactic → Tactic;
rule lastStepQuant $t ↪ #and (#repeat ($t #orelse boolIds)) #reflexivity;

symbol stepwise_skolem0: 𝕃 tactic → Tactic;
rule stepwise_skolem0 ($sk1 ⸬ ($sk2 ⸬ $sk3)) ↪ #repeat ((#and (skolemProzess $sk1) (stepwise_skolem0 ($sk2 ⸬ $sk3))) #orelse boolIds)
with stepwise_skolem0 ($sk1 ⸬ □) ↪ #and (#repeat ((skolemProzess $sk1) #orelse boolIds)) #reflexivity;

symbol stepwise_skolem: (Tactic → Tactic) → 𝕃 tactic → Tactic;
rule stepwise_skolem $t ($sk1 ⸬ ($sk2 ⸬ $sk3)) ↪ #repeat ((#and ($t $sk1) (stepwise_skolem $t ($sk2 ⸬ $sk3))) #orelse boolIds)
with stepwise_skolem $t ($sk1 ⸬ □) ↪ #and (#repeat (($t $sk1) #orelse boolIds)) #reflexivity;

symbol handleQuants (varList: 𝕃 string) (allSkolemRW : 𝕃 tactic) ≔ ((stepwise_skolem skolemProzess_∀ allSkolemRW) #orelse (move_∀_out varList)) #orelse ((move_¬∃_out varList) #orelse (stepwise_skolem skolemProzess_∃ allSkolemRW));

symbol onlyBoolIds ≔ #and (#repeat boolIds) #reflexivity;

symbol cnfTac : 𝕃 string → 𝕃 tactic → Tactic;
rule cnfTac □ □ ↪ #and (#repeat boolIds) #reflexivity
with cnfTac ($v0 ⸬ $v) □ ↪  #repeat ((generalizeQuant ($v0 ⸬ $v)) #orelse boolIds)
with cnfTac □ ($s0 ⸬ $s) ↪  stepwise_skolem skolemProzess ($s0 ⸬ $s)
with cnfTac ($v0 ⸬ $v) ($s0 ⸬ $s) ↪ #repeat ((handleQuants ($v0 ⸬ $v) ($s0 ⸬ $s)) #orelse boolIds);