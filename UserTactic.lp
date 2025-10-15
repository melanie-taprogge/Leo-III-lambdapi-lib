require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.FunExt Stdlib.PropExt Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Epsilon Leo-III-lambdapi-lib.CNFeq;


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
 protected symbol set0 : Set;
 rule τ set0 ↪ Set;
 
  
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
*  Definition of additional rules for clausification      
******************************************************************************/

opaque symbol ¬∀=∃¬ (t : Set) (p : τ (t ⤳ o)) : //lemma6
π (¬(∀ p) = (`∃ (x : τ t), ¬ (p x)))≔
begin
assume t p;
refine propExt (¬ (∀ p)) (`∃ x, ¬ (p x)) _ _
{assume h;
    refine ∨ₑ (em (`∃ x, ¬ p x)) _ _
    {assume he; refine he}
    {assume hne;
        have forall_p : Π x : τ t, π (p x)
            {assume a; refine ¬¬ₑ (p a) (λ hp, hne (∃ᵢ [t] [λ y, ¬ p y] a hp))};
        refine ⊥ₑ (h (λ a, forall_p a))}}
{assume h h2;
    refine ∃ₑ [t] [λ y, ¬ p y] h (λ a hna, hna (h2 a))}
end;

opaque symbol ¬∃=∀¬ (t : Set) (p : τ (t ⤳ o)) : // lemma7
π (¬(∃ p) = (`∀ (x : τ t), ¬ p x))≔     
begin
assume t p;
refine propExt (¬ (∃ p)) (`∀ x, ¬ p x) _ _
{assume h a ha; refine h (∃ᵢ [t] [p] a ha)}
{assume h1 h2; refine ∃ₑ [t] [p] h2 (λ a ha, (h1 a) ha)}
end;


//  Skolemisazion


opaque symbol εᵢ_rev :  Π [a: Set], Π p: (τ a → Prop),  π (p (ε p)) → π (∃ p)≔
begin
assume a p h;
refine ∃ᵢ [a] [p] (ε p) h
end;

opaque symbol ∃_skolem (a: Set) (p: τ (a ⤳ o)) :  
 π ((∃ p) = (p (ε p)))≔
begin
 assume a p;
 refine propExt (∃ p) (p (ε p)) (εᵢ [a] p) (εᵢ_rev [a] p)
end;

opaque symbol ∀_skolem (a: Set) (p: τ (a ⤳ o)) :  
π (¬ (∀ p) = ¬ (p (ε (λ x, ¬ (p x)))))≔
begin
assume a p;
rewrite ¬∀=∃¬;
refine  propExt (`∃ x, ¬ (p x)) (¬ (p (ε (λ x, ¬ (p x))))) _ _
    {assume h; refine ind_eq (eq_sym (∃_skolem a (λ x, ¬ (p x)))) (λ x, x) h}
    {assume h; refine ind_eq (∃_skolem a (λ x, ¬ (p x))) (λ x, x) h}
end;


//Quantifier Distributivity

opaque symbol ∀∧_dist_r t a (p : τ(t ⤳ o)): π ((a ∧ ∀ p) = (`∀ x, a ∧ p x))≔
begin
    assume t a p;
    refine propExt (a ∧ ∀ p) (∀(λ x, a ∧ p x)) _ _
        {assume h x;
        refine ∧ᵢ (∧ₑ₁ h) ((∧ₑ₂ h) x)}
        {assume h;
        refine ∨ₑ (em (∀ p)) _ _
            {assume h1;
            refine ∧ᵢ (∧ₑ₁ (h (el t))) h1}
            {assume h1;
            have H0: π (¬ (p (ε (λ x, ¬ (p x)))))
                {refine =⇒ (∀_skolem t p) h1};
            have H1: π (p (ε (λ x, ¬ (p x))))
                {refine ∧ₑ₂ (h (ε (λ x, ¬ (p x))))};
            refine ⊥ₑ (H0 H1)}}
end;

opaque symbol ∀∧_dist_l t a (p : τ(t ⤳ o)): π ((∀ p ∧ a) = (`∀ x,p x ∧ a))≔
begin
    assume t a p;
    refine propExt (∀ p ∧ a) (`∀ x, p x ∧ a) _ _
        {assume h0 x;
        rewrite ∧_com;
        refine (=⇒ ((∀∧_dist_r t a p)) (=⇒ (∧_com (∀ p) a) h0)) x
        }
        {assume h0;
        rewrite ∧_com;
        have H0: π (`∀ x, a ∧ p x)
            {assume x;
            rewrite ∧_com;
            refine h0 x};
        refine =⇒ (eq_sym (∀∧_dist_r t a p)) H0
        };
end;

opaque symbol ∀∨_dist_r t a (p : τ(t ⤳ o)): π ((a ∨ ∀ p) = (`∀ x, a ∨ p x))≔
begin
    assume t a p;
    refine propExt (a ∨ ∀ p) (∀(λ x, a ∨ p x)) _ _
        {assume h x;
        refine ∨ₑ h _ _
            {assume h0;
            refine ∨ᵢ₁ h0}
            {assume h0;
            refine ∨ᵢ₂ (h0 x)}}
        {assume h;
        refine ∨ₑ (em (∀ p)) _ _
            {assume h1;
            refine ∨ᵢ₂ h1}
            {assume h1;
            have H0: π (¬ (p (ε (λ x, ¬ (p x)))))
                {refine =⇒ (∀_skolem t p) h1};
            refine ∨ₑ (h (ε (λ x, ¬ (p x)))) _ _
                {assume h0;
                refine ∨ᵢ₁ h0}
                {assume h0;
                refine ⊥ₑ (H0 h0)}}}
end;

opaque symbol ∀∨_dist_l t a (p : τ(t ⤳ o)): π ((∀ p ∨ a) = (`∀ x,p x ∨ a))≔
begin
    assume t a p;
    refine propExt (∀ p ∨ a) (`∀ x,p x ∨ a) _ _
        {assume h0 x;
        rewrite ∨_com;
        refine (=⇒ ((∀∨_dist_r t a p)) (=⇒ (∨_com (∀ p) a) h0)) x}
        {assume h0;
        rewrite ∨_com;
        have H0: π (`∀ x, a ∨ p x)
            {assume x;
            rewrite ∨_com;
            refine h0 x};
        refine =⇒ (eq_sym (∀∨_dist_r t a p)) H0};
end;

opaque symbol ∀_ext [t: Set] [p q] : π(`∀ (x : τ t), p x = q x) → π ((`∀ (x: τ t), p x) = (`∀ (x: τ t), q x))≔
begin
    assume t p q h;
    refine propExt (`∀ (x: τ t), p x) (`∀ (x: τ t), q x) _ _
        {assume h1 x;
        refine =⇒ (h x) (h1 x)}
        {assume h1 x;
        refine =⇒ (eq_sym (h x)) (h1 x)}
end;

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

symbol cnfTac : 𝕃 string → 𝕃 tactic → Tactic;
rule cnfTac □ □ ↪ #and (#repeat boolIds) #reflexivity
with cnfTac ($v0 ⸬ $v) □ ↪  #repeat ((generalizeQuant ($v0 ⸬ $v)) #orelse boolIds)
with cnfTac □ ($s0 ⸬ $s) ↪  stepwise_skolem skolemProzess ($s0 ⸬ $s)
with cnfTac ($v0 ⸬ $v) ($s0 ⸬ $s) ↪ #repeat ((handleQuants ($v0 ⸬ $v) ($s0 ⸬ $s)) #orelse boolIds);