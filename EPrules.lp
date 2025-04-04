require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Classic Stdlib.HOL Stdlib.Impred Stdlib.PropExt;

///////////////////////////////////////////////////////////////////////////////////////
////////////////////////////// CALCULUS RULES /////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

////////// Extensionality  

opaque symbol PFE [T] [S] (f g : τ (S ⤳ T)) (x : τ S): 
      π (f = g) → π (f x = g x) ≔
begin
	assume T S f g x h;
    refine ind_eq h (λ y, y x = g x) (eq_refl [T] (g x))
end;

opaque symbol PBE_r x y: π(x = y) → π(x ∨ ¬ y)≔
begin
    assume x y h;
    refine ind_eq h (λ z, z ∨ ¬ y) (em y);
end;

opaque symbol PBE_l x y: π(x = y) → π(¬ x ∨ y)≔
begin
    assume x y h;
    have em_sym: π(¬ y ∨ y)
        {refine ∨ₑ(em y)  _ _ 
            {assume h2;
            refine ∨ᵢ₂ h2}
            {assume h2;
            refine ∨ᵢ₁ h2}};
    refine ind_eq h (λ z, ¬ z ∨ y) em_sym;
end;

opaque symbol NBE_p x y: π(¬(x = y)) → π(x ∨ y)≔
begin
    assume x y h1;
    refine ∨ₑ (em x) _ _
        {assume h2;
        refine ∨ᵢ₁ h2}
        {assume h2;
        have H1: π y
            {have H2: π (¬ y) → π ⊥
                {assume h3;
                have H3: π x → π y
                    {assume h4;
                    refine ⊥ₑ (h2 h4)};
                have H4: π y → π x
                    {assume h4;
                    refine ⊥ₑ (h3 h4)};
                refine h1 (propExt x y H3 H4)};
            refine ¬¬ₑ y H2};
        refine ∨ᵢ₂ H1};
end;

opaque symbol NBE_n x y: π(¬(x = y)) → π(¬ x ∨ ¬ y)≔
begin
    assume x y h1;
    refine ∨ₑ (em x) _ _
        {assume h2;
        have H1: π (y) → π ⊥
            {assume h3;
            have H2: π x → π y
                {assume h4;
                refine h3};
            have H3: π y → π x
                {assume h4;
                refine h2};
            refine h1 (propExt x y H2 H3)};
        refine ∨ᵢ₂ H1}
        {assume h2;
        refine ∨ᵢ₁ h2}
end;


////////// Equal Factoring

opaque symbol EqFact_p [T : Set] (x y z v : τ T): 
        π (x = y ∨ z = v) → π (x = y ∨ ¬ (x = z) ∨ ¬ (y = v))≔
begin
    assume T x y z v h1;
    refine ∨ₑ (em (x = y)) _ _ 
                {assume h2;
                type ∨ᵢ₁ [x = y] [¬ (x = z)] h2;
                refine ∨ᵢ₁ h2}
                {assume h3;
                refine ∨ₑ (em (x = z)) _ _ 
                    {assume h4;
                    refine ∨ₑ (em (y = v)) _ _ 
                        {assume h5;
                        have H1: π (z = v)
                            {refine ∨ₑ h1 _ _
                                {assume h6;
                                refine ⊥ₑ (h3 h6)}
                                {assume h7;
                                refine h7}};
                        have H2: π(x = v)
                            {refine ind_eq h4 (λ a, a = v) H1};
                        have H3: π(v = y)
                            {refine ind_eq h5 (λ a, v = a) (eq_refl [T] v)};
                        have H4: π(x = y)
                            {refine ind_eq H2 (λ a, a = y) H3};
                        refine ⊥ₑ (h3 H4)}
                        {assume h8;
                        refine ∨ᵢ₂ (∨ᵢ₂ h8)}}
                    {assume h9;
                    refine ∨ᵢ₂ (∨ᵢ₁ h9)}}
end;

opaque symbol EqFact_n [T] x y z v: 
        π (¬ (x = y) ∨ ¬ (z = v)) → π (¬ (x = y) ∨ ¬ (x = z) ∨ ¬ (y = v))≔
begin
    assume T x y z v h1;
    refine (∨ₑ (em (x = y)) _ _ )
                {assume h3;
                refine (∨ₑ (em (x = z)) _ _ ) 
                    {assume h4;
                    refine (∨ₑ (em (y = v)) _ _ )
                        {assume h5;
                        have H1: π(z = x)
                            {refine ind_eq h4 (λ a, z = a) (eq_refl [T] z)};
                        have H2: π(z = y)
                            {refine ind_eq H1 (λ a, a = y) h3};
                        have H3: π( ¬ (z = v))
                            {refine ∨ₑ h1 _ _
                                {assume h6;
                                refine ⊥ₑ (h6 h3)}
                                {assume h6;
                                refine h6}};
                        have H4: π(z = v)
                            {refine ind_eq  H2 (λ a, a = v) h5};
                        refine ⊥ₑ (H3 H4)}
                        {assume h6;
                        refine ∨ᵢ₂ (∨ᵢ₂ h6)}}
                    {assume h4;
                    refine ∨ᵢ₂ (∨ᵢ₁  h4)}}
                {assume h3;
                refine ∨ᵢ₁ h3}
end;