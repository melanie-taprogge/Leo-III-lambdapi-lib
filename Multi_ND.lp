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

symbol rem [a : Set]: 𝕃 a → ℕ → 𝕃 a;
rule rem ($l0 ⸬ $l) ($n +1) ↪ ($l0 ⸬ (rem $l $n))
with rem  ($l0 ⸬ $l) 0 ↪ $l
with rem □ _ ↪ □;

symbol ∨ₑₙ (n : ℕ) (c : 𝕃 o) (r : Prop) : π(disj c) → π((literal c n ⇒ r)) → π((disj(rem c n)) ⇒ r) → π r ≔
begin
    induction
        {induction
            {assume x h0 h1 h2; refine ⊥ₑ h0}
            {assume l0 l h0 r h1 h2 h3;
             refine ∨ₑ (=⇒ (disj_correct l0 l) h1) _ _
                {assume h4; refine h2 h4}
                {assume h4; refine h3 h4}}}
        {assume n h0; induction
            {assume r h1 h2 h3; refine ⊥ₑ h1}
            {assume l0 l h1 r h2 h3 h4;
            have H1 : π ((l0  ∨ (disj (rem l n))) ⇒ r)
                    {rewrite left disj_correct; refine h4};
            refine ∨ₑ (em l0) _ _
                {assume h5;
                refine H1 ((∨ᵢ₁ [l0] [disj (rem l n)]) h5)}
                {assume h5;
                have l0is⊥ : π (⊥ = l0)
                    {refine propExt ⊥ l0 _ _
                        {assume h6; refine ⊥ₑ h6}
                         {assume h6; refine h5 h6}};
                refine h0 l r _ h3 _
                    {rewrite left ⊥∨; rewrite l0is⊥;
                    rewrite left disj_correct l0 l; refine h2}
                    {rewrite left ⊥∨ (disj (rem l n)); 
                    rewrite l0is⊥; refine H1}}}}        
end;