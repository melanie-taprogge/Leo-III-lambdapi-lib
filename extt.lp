require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.HOL Stdlib.Impred;

symbol propExt x y : (π x → π y) → (π y → π x) → π (x = y);
symbol funExt [T S] (f g : (τ (T ⤳ S))) : π(∀(λ x, (f x) = (g x))) → π(f = g);

symbol em x : π((x ∨ ¬ x));

opaque symbol npp x : π(¬ ¬ x) → π x ≔
begin
    assume x h1;
    refine ∨ₑ (em x) _ _
        {assume h2;
        refine h2}
        {assume h2;
        refine ⊥ₑ (h1 h2)}
end;