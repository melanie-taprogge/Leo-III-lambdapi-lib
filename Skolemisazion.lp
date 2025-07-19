require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.PropExt Stdlib.Epsilon;

opaque symbol ¬∀=∃¬ (t : Set) (p : τ (t ⤳ o)) : 
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

opaque symbol ¬∃=∀¬ (t : Set) (p : τ (t ⤳ o)) : 
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

opaque symbol ∀_ext [t: Set] p q : π(`∀ (x : τ t), p x = q x) → π ((`∀ (x: τ t), p x) = (`∀ (x: τ t), q x))≔
begin
    assume t p q h;
    refine propExt (`∀ (x: τ t), p x) (`∀ (x: τ t), q x) _ _
        {assume h1 x;
        refine =⇒ (h x) (h1 x)}
        {assume h1 x;
        refine =⇒ (eq_sym (h x)) (h1 x)}
end;
