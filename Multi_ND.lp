require open Leo-III-lambdapi-lib.MetaTheorems;
require open Stdlib.PropExt;

/* 
Library on versions of the natural deduction rules over more than just two terms
*/

////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////// ⇒ //////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


symbol multi_impl : 𝕃 o → τ o → Prop;
rule multi_impl ($p0 ⸬ $p) $p1 ↪ $p0 ⇒ (multi_impl $p $p1)
with multi_impl □ $p0 ↪ $p0;

symbol multi_impl_correct (p : 𝕃 o) (p0 p1: Prop): π ((multi_impl (p0 ⸬ p) p1) = (p0 ⇒ multi_impl p p1)) ≔
begin
    induction
        {simplify; assume x0 x1; reflexivity}
        {simplify; assume p0 p h0 p1 p2;
        rewrite h0 p0; reflexivity}
end;


////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////// ∨ //////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

symbol ∨ᵢₙ₂ (c0 : 𝕃 o) (c1 : 𝕃 o) : π (disj c1) → π (disj (c0 ++ c1))≔
begin
    induction
        {assume x h;
        refine h}
        {assume x0 l0 h0 l1 h1; simplify;
        rewrite disj_correct;
        refine ∨ᵢ₂ (h0 l1 h1)}
end;

symbol ∨ᵢₙ₁ (c0 : 𝕃 o) (c1 : 𝕃 o) : π (disj c0) → π (disj (c0 ++ c1))≔
begin
    induction
        {assume x h; refine ⊥ₑ h}
        {assume x0 l h0 x1; 
        type h0 x1;
        rewrite disj_correct; assume h1; 
        simplify; 
        rewrite disj_correct;
        refine ∨ₑ h1 _ _
            {assume h2;
            refine ∨ᵢ₁ h2}
            {assume h2;
            refine ∨ᵢ₂ (h0 x1 h2)}}
end;

