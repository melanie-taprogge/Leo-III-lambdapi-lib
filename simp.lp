require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Classic Stdlib.Bool Stdlib.List Stdlib.HOL Stdlib.Impred Leo-III-lambdapi-lib.extt Leo-III-lambdapi-lib.accessoryRules;

///////////////////////////////////////////////////////////////////////////////////////
////////////////////////////// SIMPLIFICATION RULES ///////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////// 

opaque symbol simp1 x: (π (x = (x ∨ x)))≔
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

opaque symbol simp2 x: (π (x = (x ∧ x)))≔
begin
    assume x;
    refine propExt x (x ∧ x) _ _ 
        {assume h1;
        refine ∧ᵢ h1 h1}
        {assume h1;
        refine ∧ₑ₁ h1}
end;

opaque symbol simp3 x: (π (⊤ = ((¬ x) ∨ x)))≔
begin
    assume x;
    refine propExt ⊤ ((¬ x) ∨ x) _ _ 
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

opaque symbol simp4 x: (π (⊥ = ((¬ x) ∧ x)))≔
begin
    assume x;
    refine propExt ⊥ ((¬ x) ∧ x) _ _ 
        {assume h1;
        refine ⊥ₑ h1}
        {assume h1;
        refine (∧ₑ₁ h1) (∧ₑ₂ h1)}
end;

opaque symbol simp5 x: (π (⊤ = (x ∨ ⊤)))≔
begin
    assume x;
    refine propExt ⊤ (x ∨ ⊤) _ _ 
        {assume h2;
        refine ∨ᵢ₂ h2}
            {assume h1;
        refine ⊤ᵢ}
end;

opaque symbol simp6 x: (π (x = (x ∧ ⊤)))≔
begin
    assume x;
    refine propExt x (x ∧ ⊤) _ _ 
        {assume h1;
        refine ∧ᵢ h1 ⊤ᵢ}
        {assume h1;
        refine ∧ₑ₁ h1}
end;

opaque symbol simp7 x: (π (x = (x ∨ ⊥)))≔
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

opaque symbol simp8 x: (π (⊥ = (x ∧ ⊥)))≔
begin
    assume x;
    refine propExt ⊥ (x ∧ ⊥) _ _ 
        {assume h1;
        type ⊥ₑ h1;
        refine ∧ᵢ (⊥ₑ h1) h1}
        {assume h1;
        refine ∧ₑ₂ h1}
end;

opaque symbol simp9 (T : Set) (x : τ T): (π ( ⊤ = (x = x)))≔
begin
    assume T x;
    refine propExt ⊤ (x = x) _ _ 
        {assume h1;
        refine eq_refl x}
        {assume h1;
        refine ⊤ᵢ}
end;

opaque symbol simp10 (T : Set) (x : τ T): (π (⊥ = (¬ (x = x))))≔
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

opaque symbol simp11 x: (π (x = (x = ⊤)))≔
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

opaque symbol simp12 x: (π ((¬ x) = (¬(x = ⊤))))≔
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

opaque symbol simp15 : (π (⊤ = (¬ ⊥)))≔
begin
    refine propExt ⊤ (¬ ⊥) _ _ 
        {assume h1 h2;
        refine h2}
        {assume h1;
        refine ⊤ᵢ}
end;

opaque symbol simp16 : (π (⊥ = (¬ ⊤)))≔
begin
    refine propExt ⊥ (¬ ⊤) _ _ 
        {assume h1;
        refine ⊥ₑ h1}
        {assume h1;
        refine h1 ⊤ᵢ}
end;

opaque symbol simp17 x: (π (x = (¬ ¬ x)))≔
begin
    assume x;
    refine propExt x (¬ ¬ x) _ _ 
        {assume h1 h2;
        refine h2 h1}
        {assume h1;
        refine ¬¬ₑ x h1}
end;

