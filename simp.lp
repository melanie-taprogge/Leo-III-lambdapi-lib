require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Classic Stdlib.Bool Stdlib.List Stdlib.HOL Stdlib.Impred Leo-III-lambdapi-lib.extt Leo-III-lambdapi-lib.accessoryRules;

///////////////////////////////////////////////////////////////////////////////////////
////////////////////////////// SIMPLIFICATION RULES ///////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////// 

// Simplifications of Idempotence and Contradiction for ∧ and ∨

opaque symbol ∨_idem x: π (x = (x ∨ x))≔
begin
    assume x;
    refine propExt x (x ∨ x) _ _ 
        {assume h2;
        refine ∨ᵢ₁ h2}
        {assume h1;
        refine ∨ₑ h1 _ _
            {assume h2;
            refine h2}
            {assume h2;
            refine h2}}
end;

opaque symbol ∧_idem x: π (x = (x ∧ x))≔
begin
    assume x;
    refine propExt x (x ∧ x) _ _ 
        {assume h1;
        refine ∧ᵢ h1 h1}
        {assume h1;
        refine ∧ₑ₁ h1}
end;

opaque symbol ∧_contra x: π (⊥ = ((¬ x) ∧ x))≔
begin
    assume x;
    refine propExt ⊥ ((¬ x) ∧ x) _ _ 
        {assume h1;
        refine ⊥ₑ h1}
        {assume h1;
        refine (∧ₑ₁ h1) (∧ₑ₂ h1)}
end;


// Simplifications of Conjunction and Disjunction with ⊤ and ⊥

opaque symbol ∨⊤ x: π (⊤ = (x ∨ ⊤))≔
begin
    assume x;
    refine propExt ⊤ (x ∨ ⊤) _ _ 
        {assume h2;
        refine ∨ᵢ₂ h2}
            {assume h1;
        refine ⊤ᵢ}
end;

opaque symbol ∧⊤ x: π (x = (x ∧ ⊤))≔
begin
    assume x;
    refine propExt x (x ∧ ⊤) _ _ 
        {assume h1;
        refine ∧ᵢ h1 ⊤ᵢ}
        {assume h1;
        refine ∧ₑ₁ h1}
end;

opaque symbol ∨⊥ x: π (x = (x ∨ ⊥))≔
begin
    assume x;
    refine propExt x (x ∨ ⊥) _ _ 
        {assume h1;
        refine ∨ᵢ₁ h1}
        {assume h1;
        refine ∨ₑ h1 _ _
            {assume h2;
            refine h2}
            {assume h2;
            refine ⊥ₑ h2}}
end;

opaque symbol ∧⊥ x: π (⊥ = (x ∧ ⊥))≔
begin
    assume x;
    refine propExt ⊥ (x ∧ ⊥) _ _ 
        {assume h1;
        type ⊥ₑ h1;
        refine ∧ᵢ (⊥ₑ h1) h1}
        {assume h1;
        refine ∧ₑ₂ h1}
end;


// Simplifications of negated ⊤ and ⊥

opaque symbol ¬⊥ : π (⊤ = ¬ ⊥)≔
begin
    refine propExt ⊤ (¬ ⊥) _ _ 
        {assume h1 h2;
        refine h2}
        {assume h1;
        refine ⊤ᵢ}
end;

opaque symbol ¬⊤ : π (⊥ = ¬ ⊤)≔
begin
    refine propExt ⊥ (¬ ⊤) _ _ 
        {assume h1;
        refine ⊥ₑ h1}
        {assume h1;
        refine h1 ⊤ᵢ}
end;


// Simplifications of equalities

opaque symbol eqxx (T : Set) (x : τ T): π ( ⊤ = (x = x))≔
begin
    assume T x;
    refine propExt ⊤ (x = x) _ _ 
        {assume h1;
        refine eq_refl x}
        {assume h1;
        refine ⊤ᵢ}
end;

opaque symbol ¬eqxx (T : Set) (x : τ T): π (⊥ = ¬ (x = x))≔
begin
    assume T x;
    refine propExt ⊥ (¬ (x = x)) _ _ 
        {assume h1;
        refine ⊥ₑ h1}
        {assume h1;
        have H1: π (x = x) → π ⊥
            {assume h2;
            refine h1 h2};
        refine H1 (eq_refl [T] x)}
end;

opaque symbol eq⊤ x: π (x = (x = ⊤))≔
begin
    assume x;
    refine propExt x (x = ⊤) _ _ 
        {assume h1;
        refine propExt x ⊤ _ _
            {assume h2;
            refine ⊤ᵢ}
            {assume h2;
            refine h1}}
        {assume h1;
        refine (ind_eq h1 (λ z: Prop, z)) ⊤ᵢ}
end;

opaque symbol ¬eq⊤ x: π (¬ x = ¬(x = ⊤))≔
begin
    assume x;
    refine propExt  (¬ x) (¬(x = ⊤)) _ _ 
        {assume h1 h2;
            have H1_1: π x
                {refine ind_eq h2 (λ z: Prop, z) ⊤ᵢ};
            refine h1 H1_1}
        {assume h1 h2;
        refine h1 (propExt x ⊤ _ _)
                {assume h3;
                refine ⊤ᵢ}
                {assume h3;
                refine h2}}
end;


// Simplifications reflecting Classical Principles

opaque symbol em_eq x: π (⊤ = (¬ x ∨ x))≔
begin
    assume x;
    refine propExt ⊤ (¬ x ∨ x) _ _ 
        {assume h2;
        have em_sym: π(¬ x ∨ x)
        {refine ∨ₑ (em x) _ _
            {assume h3;
            refine ∨ᵢ₂ h3}
            {assume h3;
            refine ∨ᵢ₁ h3}};
        refine em_sym}
        {assume h1;
        refine ⊤ᵢ}
end;

opaque symbol ¬¬ₑ_eq x: π (x = ¬ ¬ x)≔
begin
    assume x;
    refine propExt x (¬ ¬ x) _ _ 
        {assume h1 h2;
        refine h2 h1}
        {assume h1;
        refine ¬¬ₑ x h1}
end;

