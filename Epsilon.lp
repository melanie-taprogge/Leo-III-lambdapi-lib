require open Stdlib.FOL Stdlib.HOL Stdlib.Impred;

symbol ε [a:Set] : τ ((a ⤳ o) ⤳ a);
symbol εᵢ [a:Set] (p:τ a → Prop) : π (∃ p) → π (p (ε p));

// Here, we just restate epsilon in terms of the object level types to avoid current Labmapi unification bug.
// This declaration is equivalent to the standanrdlibrary version:
// symbol ε [a:Set] : (τ a → Prop) → τ a;
// symbol εᵢ [a:Set] (p:τ a → Prop) : π (∃ p) → π (p (ε p));