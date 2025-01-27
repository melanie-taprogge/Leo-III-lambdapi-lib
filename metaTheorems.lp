/* Library on Meta-Theorems for Disjunctions

-------------------

The library aims to prove the following meta-theorems for disjunctions:

** Permutation Theorem:
   The theorem is instantiated with:
   - A list of natural numbers representing a disjunction.
   - A list of terms of type `o` representing a clause.

   The theorem verifies that the permuted clause still contains all literals of the original clause. 
   If so, it maps the disjunction of the original clause to the disjunction after the permutation.

** Double Literal Deletion Theorem:
   The theorem is instantiated with three lists:
   - A list of natural numbers representing the indices of literals in the original list. 
     For literals occurring multiple times, the index of the first occurrence is used for all of the
     subsequent occurrences. For example, for `π (l0 ∨ l1 ∨ l2 ∨ l1)`, this list would be `(0, 1, 2, 1)`.
   - A second list of natural numbers indicating the desired positions of the literals in the clause.
     If for instance the second occurrence of `l1` in `π (l0 ∨ l1 ∨ l2 ∨ l1)` should be deleted, the 
     derived clause would be `π (l0 ∨ l1 ∨ l2)`, and the list that must be provided would be (0, 1, 2).
     To delete the first occurrence of `l1`, and derive the clause `π (l0 ∨ l2 ∨ l1)`, the list would 
     be (0, 2, 1).
   3. A list of terms of type `o`, representing literals.

   The resulting theorem verifies if each literal from the original clause is still present at least once 
   in the derived clause. If so, it maps the disjunction of the original literals to the disjunction after 
   the desired double literal deletion. This approach allows multiple identical literals to be deleted at once.

** Transformation Theorem:
   This theorem is useful when a rule is applied to only one literal of a clause. 
   For example, consider the clause `π (l0 ∨ l1 ∨ l2 ∨ l3)` and an inference rule `π l2 → π l2'`. 
   The transformation theorem can be instantiated with:
   - The list of terms of type `o` representing the original clause.
   - The position of the literal being affected.
   - The inference rule.

   The resulting term maps the original disjunction to one with the transformed literal.

---

** General Concept:
   The general idea behind the permutation and double literal deletion theorems is to evaluate a list of natural 
   numbers representing the positions of literals after respective operations with respect to the list of literals. 
   A computation ensures the operation is admissible:
   - In the case of permutations, all literals must still be present in the permuted clause.
   - In the case of double literal deletion, each literal must still be present at least once.
   If these conditions are fulfilled, the corresponding argument in the theorem will compute to `π ⊤` and can simply
   be instantiated with `⊤ᵢ` (examples are given below).

---

** Defined Operations:
                        `indexes l`: Returns a list of the indices of the list `l`.
                      `eval n l`: Returns the element of the list `l` at index `n`.
                `eval_list ln l`: Takes as arguments a list `ln` of natural numbers and a list `l` and 
                                  returns a list of  the elements of `l` ordered according to the indices in `ln`.
                        `disj l`: Returns the disjunction of all literals in the list `l`.
       `bincludes [a] eqb l1 l2`: For two lists `l1` and `l2` of type `a` and a boolean equality relation `eqb` 
                                  for elements of type `a`, this operation returns `true` if `l2` includes all 
                                  elements of `l1`, and `false` otherwise.
      `preserves_contents ln lo`: Takes a list of natural numbers (`ln`) and a list of terms of type `o` (`lo`) 
                                  as arguments. Returns `true` if every index of `lo` is included in `ln`.
*/

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Impred;

// eval 

symbol eval : τ nat → 𝕃 o → τ o;
rule eval $n $list ↪ nth ⊥ $list $n;

assert l0 l1 l2 ⊢ eval 1 (l0 ⸬ l1 ⸬ l2 ⸬ l1 ⸬ □) ≡ l1;

opaque symbol eval_ext (l: 𝕃 o) (l0 : τ o) (n: τ nat) : 
    π (eval n l) → π (eval (n +1) (l0 ⸬ l)) ≔
begin
    assume l l0 n;
    simplify;
    assume h1;
    refine h1
end;


// eval_list

symbol eval_list: 𝕃 nat → 𝕃 o → 𝕃 o;
rule eval_list ($n ⸬ $l) $list ↪ (nth ⊥ $list $n) ⸬ (eval_list $l $list)
with eval_list □ _ ↪ □;

assert l0 l1 l2 ⊢ eval_list (1 ⸬ 2 ⸬ 0 ⸬ 3 ⸬ □) (l0 ⸬ l1 ⸬ l2  ⸬ l1 ⸬ □) ≡ l1 ⸬ (l2  ⸬ (l0 ⸬ (l1 ⸬ □)));


// disj

symbol disj : 𝕃 o → τ o;
rule disj ($l1 ⸬ ($c ⸬ $l)) ↪ ($l1 ∨ disj ($c ⸬ $l))
with disj ($l1 ⸬ □) ↪ $l1 
with disj □ ↪ ⊥;

assert l0 l1 l2 ⊢ π (disj (l0 ⸬ l1 ⸬ l2  ⸬ l1 ⸬ □)) ≡ π (l0 ∨ (l1 ∨ (l2  ∨ l1)));

opaque symbol disj_head (l0 : τ o) (l : 𝕃 o) : 
    π (l0) → π (disj (l0 ⸬ l)) ≔
begin
    assume l0;
    induction
        {assume h1;
        refine h1}   
        {assume x0 l1 h1; 
        assume h2; 
        refine ∨ᵢ₁ h2}
end; 

opaque symbol disj_tail (l0 : τ o) (l : 𝕃 o) : 
    π (disj l) → π (disj (l0 ⸬ l)) ≔
begin
    assume l0;
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume x1 l1 h1 h2;
        refine ∨ᵢ₂ h2}
end;

opaque symbol disj_correct (l0 : τ o) (l : 𝕃 o) : 
    π (disj (l0 ⸬ l)) → π (l0 ∨ disj l) ≔
begin
    assume l0;
    induction
        {assume h1;
        refine ∨ᵢ₁ h1}
        {assume x1 l1 h1 h2;
        refine h2}
end;

opaque symbol lit_imp_disj (lit_list: 𝕃 o) (pos_list: 𝕃 nat) : 
    π (∃(λ x, (eval x lit_list) ∧ (∈ eqn x pos_list))) → π (disj (eval_list pos_list lit_list)) ≔
begin
    assume lit_list;
    induction
        {simplify;
        assume h1;
        have H0: (Π x: τ nat, π ((λ x1, nth ⊥ lit_list x1 ∧ ⊥) x) → π ⊥)
            {assume x h2;
            refine ∧ₑ₂ h2};
        refine ∃ₑ h1 H0}
        {assume n l;
        simplify;
        assume h1 h2;
        have H1 : Π x: τ nat, π ((λ x1, nth ⊥ lit_list x1 ∧ (eqn x1 n or ∈ eqn x1 l)) x) → π (disj (nth ⊥ lit_list n ⸬ eval_list l lit_list))
            {assume m h3;
            have H0 : π ((eqn m n) ∨ (∈ eqn m l))
                {refine ∨_istrue [eqn m n] [∈ eqn m l] (∧ₑ₂ h3)};
            have H1 : π (eqn m n) → π (disj (nth ⊥ lit_list n ⸬ eval_list l lit_list))
                {assume h4;
                have H1_0 : π (nth ⊥ lit_list n)
                    {have H1_0_0 : π (n = m)
                        {symmetry;
                        refine eqn_correct m n h4};
                    rewrite H1_0_0;
                    refine ∧ₑ₁ h3};
                refine disj_head (nth ⊥ lit_list n) (eval_list l lit_list) H1_0};
            have H2 : π (∈ eqn m l) → π (disj (nth ⊥ lit_list n ⸬ eval_list l lit_list))
                {assume h4;
                have H2_0 : π `∃ x, nth ⊥ lit_list x ∧ (∈ eqn x l)
                    {have H2_0_0 : π ((λ x, nth ⊥ lit_list x ∧ (∈ eqn x l)) m)
                        {refine ∧ᵢ (∧ₑ₁ h3) h4};
                    refine ∃ᵢ m H2_0_0};
                refine disj_tail (nth ⊥ lit_list n) (eval_list l lit_list) (h1 H2_0)};
            refine ∨ₑ H0 H1 H2
            };
        refine ∃ₑ h2 H1}   
end;

opaque symbol disj_imp_lit (l: 𝕃 o) : 
    π (disj l) → π (∃(λ (x : τ nat), (eval x l) ∧ (∈ eqn x (indexes l)))) ≔
begin
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume l0 l h1 h2;
        have H0: π (l0 ∨ disj l)
            {refine disj_correct l0 l h2};
        have H1: π l0 → π (`∃ x, (eval x (l0 ⸬ l)) ∧ (∈ eqn x (indexes (l0 ⸬ l))))
            {assume h3;
            have H1_0 : π (eval 0 (l0 ⸬ l))
                {simplify;
                refine h3};
            have H1_1 : π ((λ x, eval x (l0 ⸬ l) ∧ (∈ eqn x (indexes (l0 ⸬ l)))) 0)
                {simplify;
                refine ∧ᵢ H1_0 (0∈indexes⸬ l0 l)};
            refine ∃ᵢ [nat] [(λ x, eval x (l0 ⸬ l) ∧ (∈ eqn x (indexes (l0 ⸬ l))))] 0 H1_1};
        have H2: π (disj l) → π (`∃ x, (eval x (l0 ⸬ l)) ∧ (∈ eqn x (indexes (l0 ⸬ l))))
            {assume h3;
            have H2_0 : Π x0 , π ((λ x, eval x l ∧ (∈ eqn x (indexes l))) x0) → π (`∃ x, (eval x (l0 ⸬ l)) ∧ (∈ eqn x (indexes (l0 ⸬ l))))
                {assume n h4;
                have H2_0_0 : π ((λ x , (eval x (l0 ⸬ l)) ∧ (∈ eqn x (indexes (l0 ⸬ l)))) (n +1))
                    {refine ∧ᵢ (eval_ext l l0 n ((∧ₑ₁ h4))) (+1∈indexes⸬ o n l l0 ((∧ₑ₂ h4)))};
                refine ∃ᵢ [nat] [λ x , (eval x (l0 ⸬ l)) ∧ (∈ eqn x (indexes (l0 ⸬ l)))] (n +1) H2_0_0
                };
            refine ∃ₑ (h1 h3) [`∃ x, (eval x (l0 ⸬ l)) ∧ (∈ eqn x (indexes (l0 ⸬ l)))] H2_0};
        refine ∨ₑ H0 H1 H2};
end;

opaque symbol x_in_x⸬ [a] (l: 𝕃 a) (l0 : τ a) (beq: τ a → τ a → 𝔹) : 
    (Π x, π (beq x x)) → π (∈ beq l0 (l0 ⸬ l)) ≔
begin
    assume a l l0 beq h1;
    refine orᵢ₁ [beq l0 l0] (∈ beq l0 l) (h1 l0)
end;

opaque symbol in⸬ [a] (beq: τ a → τ a → 𝔹) (n m: τ a) (l: 𝕃 a) : 
    π (∈ beq n l) → π (∈ beq n (m ⸬ l)) ≔
begin
    assume a beq n m;
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume n0 l;
        assume h1 h2;
        have H0: π (beq n n0) →  π (beq n m or (beq n n0 or ∈ beq n l))
            {assume h3;
            refine orᵢ₂ (beq n m) [beq n n0 or ∈ beq n l] (orᵢ₁ [beq n n0] (∈ beq n l) h3)};
        have H1: π (∈ beq n l) →  π (beq n m or (beq n n0 or ∈ beq n l))
            {assume h3;
            refine orᵢ₂ (beq n m) [beq n n0 or ∈ beq n l] (orᵢ₂ (beq n n0) [∈ beq n l] h3)};
        refine orₑ [beq n n0] [∈ beq n l] (beq n m or (beq n n0 or ∈ beq n l)) h2 H0 H1}
end;

opaque symbol disj_imp_lit_pos (lit_list: 𝕃 o) (pos_list: 𝕃 nat): 
    π (disj (eval_list pos_list lit_list)) → π (∃(λ (x : τ nat), (eval x lit_list) ∧ (∈ eqn x pos_list))) ≔
begin
    assume lit_list;
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume l0 pos_list;
        assume h1 h2;
        have H0: π ((nth ⊥ lit_list l0) ∨ disj (eval_list pos_list lit_list))
            {refine disj_correct (nth ⊥ lit_list l0) (eval_list pos_list lit_list) h2};
        have H1: π (nth ⊥ lit_list l0) → π (`∃ x, eval x lit_list ∧ (∈ eqn x (l0 ⸬ pos_list)))
            {assume h3;
            have H1_0 : π (eval l0 lit_list)
                {refine h3};
            have H1_1 : π ((λ x, eval x lit_list ∧ (∈ eqn x (l0 ⸬ pos_list))) l0)
                {refine ∧ᵢ H1_0 (x_in_x⸬ pos_list l0 eqn (λ x, (eqn_complete x x (eq_refl x))))};
        refine ∃ᵢ [nat] [λ x, eval x lit_list ∧ (∈ eqn x (l0 ⸬ pos_list))] l0 H1_1};
        have H2: π (disj (eval_list pos_list lit_list)) → π (`∃ x, eval x lit_list ∧ (∈ eqn x (l0 ⸬ pos_list)))
            {assume h3;
            have H2_0: (Π x: τ nat, π ((λ x1, eval x1 lit_list ∧ (∈ eqn x1 pos_list)) x) → π (`∃ x1, eval x1 lit_list ∧ (∈ eqn x1 (l0 ⸬ pos_list))))
                {assume n h4;
                have H2_0_0 : π ((λ x, eval x lit_list ∧ (∈ eqn x (l0 ⸬ pos_list))) n)
                    {refine ∧ᵢ (∧ₑ₁ h4) (in⸬ eqn n l0 pos_list (∧ₑ₂ h4))};
                refine ∃ᵢ [nat]  [λ x , eval x lit_list ∧ (∈ eqn x (l0 ⸬ pos_list))] n H2_0_0};
            refine ∃ₑ (h1 h3) [`∃ x, eval x lit_list ∧ (∈ eqn x (l0 ⸬ pos_list))] H2_0};    
        refine ∨ₑ H0 H1 H2}
end;


// bincludes

symbol bincludes  [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;
rule bincludes $beq ($k0 ⸬ $k) $l ↪ (∈ $beq $k0 $l) and (bincludes $beq $k $l)
with bincludes _ □ _ ↪ true;

assert ⊢ bincludes eqn (0 ⸬ 1 ⸬ □) (1 ⸬ 2 ⸬ 0 ⸬ 3 ⸬ □) ≡ true;

opaque symbol bincludes_el (n: τ nat) (σ: 𝕃 nat) (ln: 𝕃 nat): 
    π (bincludes eqn ln σ) → π (∈ eqn n ln) → π (∈ eqn n σ) ≔
begin
    assume n σ;
    induction
        {assume h1 h2;
        refine ⊥ₑ h2}
        {assume m ln h1 h2 h3;
        have H1: π (eqn n m) → π (∈ eqn n σ) 
            {assume h4;
            have H1_0 : π (n = m)
                {refine eqn_correct n m h4};
            rewrite H1_0;
            refine andₑ₁ [∈ eqn m σ] [bincludes eqn ln σ] h2};
        have H2: π (∈ eqn n ln) → π (∈ eqn n σ)
            {assume h4;
            refine h1 (andₑ₂ [∈ eqn m σ] [bincludes eqn ln σ] h2) h4};
        refine orₑ [eqn n m] [∈ eqn n ln] (∈ eqn n σ) h3 H1 H2}
end;


// preserves_contents

symbol preserves_contents: 𝕃 nat → 𝕃 o → 𝔹;
rule preserves_contents  $f $l ↪ bincludes eqn (indexes $l) $f;

assert l0 l1 l2 ⊢ preserves_contents (1 ⸬ 2 ⸬ 0 ⸬ 3 ⸬ □) (l0 ⸬ l1 ⸬ l2 ⸬ l1 ⸬ □) ≡ true;

opaque symbol preserves_contents_el (n: τ nat) (σ : 𝕃 nat) (l: 𝕃 o) : 
    π (preserves_contents σ l) →  π (∈ eqn n (indexes l)) → π (∈ eqn n σ) ≔
begin
    assume n σ l;
    simplify;
    assume h1 h2;
    refine bincludes_el n σ (indexes l) h1 h2;   
end;


////////////////////////////////////////////////////////////////////////////////
///////////////////////////////// meta-therems /////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// permutation theorem 

opaque symbol perm_theorem (σ : 𝕃 nat) (c: 𝕃 o) : 
    π (preserves_contents σ c) → π(disj c) → π(disj (eval_list σ c)) ≔
begin
    assume σ c h1 h2;

    have H1: (Π x: τ nat, π ((λ x1, (eval x1 c) ∧ (∈ eqn x1 (indexes c))) x) → π (∃(λ y ,(eval y c) ∧ (∈ eqn y σ))))
        {assume x0 h3;
        refine (∃ᵢ [nat] [λ y ,(eval y c) ∧ (∈ eqn y σ)] x0) (∧ᵢ (∧ₑ₁ h3) (preserves_contents_el x0 σ c h1 (∧ₑ₂ h3)))};
    
    have H2: π (∃(λ y ,(eval y c) ∧ (∈ eqn y σ)))
        {refine ∃ₑ (disj_imp_lit c h2) H1};

    refine  lit_imp_disj c σ H2;
end;

assert l0 l1 l2 ⊢ perm_theorem (1 ⸬ 2 ⸬ 0 ⸬ 3 ⸬ □) (l0 ⸬ l1 ⸬ l2 ⸬ l0 ⸬ □) ⊤ᵢ : π (l0 ∨ l1 ∨ l2 ∨ l0) → π (l1 ∨ l2 ∨ l0 ∨ l0);


// double literal deletion theorem

opaque symbol double_lit_del_theorem (id_list : 𝕃 nat) (output_list : 𝕃 nat) (c: 𝕃 o) : 
    π (bincludes eqn id_list output_list) → π(disj (eval_list id_list c)) → π(disj (eval_list output_list c)) ≔
begin
    assume id_list output_list c h1 h2;
    refine lit_imp_disj c output_list _;
    refine ∃ₑ (disj_imp_lit_pos c id_list h2) _;
    assume n h3;
    refine (∃ᵢ [nat] [λ x, eval x c ∧ (∈ eqn x output_list)] n) (∧ᵢ (∧ₑ₁ h3) (bincludes_el n output_list id_list h1 (∧ₑ₂ h3)))
end;

assert l0 l1 l2 ⊢ double_lit_del_theorem (0 ⸬ 1 ⸬ 2 ⸬ 1 ⸬ □) (0 ⸬ 1 ⸬ 2 ⸬ □) (l0 ⸬ l1 ⸬ l2 ⸬ l1 ⸬ □) ⊤ᵢ : π (l0 ∨ l1 ∨ l2 ∨ l1) → π (l0 ∨ l1 ∨ l2);


// transformation theorem 

opaque symbol transformation_theorem [l : τ o] (c: 𝕃 o) (n : τ nat) : 
    π ((nth ⊥ c n) ⇒ l) → π (disj c) → π (disj (set_nth ⊥ c n l)) ≔
begin
    assume l;
    induction
        {simplify;
        assume x h1 h2;
        refine ⊥ₑ h2}
        {assume x clause h1;
        induction
            {simplify;
            assume h2 h3;
            have H0: π (x ∨ (disj clause))
                {refine disj_correct x clause h3};
            have H1: π x → π (disj (l ⸬ clause))
                {assume h4;
                refine disj_head l clause (h2 h4)};
            have H2: π (disj clause) → π (disj (l ⸬ clause))
                {assume h4;
                refine disj_tail l clause h4};   
            refine ∨ₑ H0 H1 H2}
            {assume n h2 h3 h4;
            have H00: π (x ∨ (disj clause)) 
                {refine disj_correct x clause h4};
            have H10: π x → π (disj (x ⸬ set_nth ⊥ clause n l))
                {assume h5;
                refine disj_head x (set_nth ⊥ clause n l) h5};
            have H20:  π (disj clause) → π (disj (x ⸬ set_nth ⊥ clause n l))
                {assume h5;
                have H2_0 : π (disj (set_nth ⊥ clause n l))
                    {refine h1 n h3 h5};
                refine disj_tail x (set_nth ⊥ clause n l) H2_0};
            refine ∨ₑ H00 H10 H20}}
end;

assert l0 l1 l2 l2' ⊢ transformation_theorem [l2'] (l0 ⸬ l1 ⸬ l2 ⸬ l1 ⸬ □) 2 : (π l2 → π l2') →  π (l0 ∨ l1 ∨ l2 ∨ l1) → π (l0 ∨ l1 ∨ l2' ∨ l1);
