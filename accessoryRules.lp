require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Classic Stdlib.Bool Stdlib.List Stdlib.HOL Stdlib.Impred Leo-III-lambdapi-lib.extt;

///////////////////////////////////////////////////////////////////////////////////////
////////////////////////////// ACCESSORY RULES ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

////////// Transforming Literals to Their Equational and Non-Equational Forms

opaque symbol posPropPosEq x: (π (x = (x = ⊤)))≔
begin
    assume x;
    refine propExt x (x = ⊤) _ _
        {assume h1;
        refine propExt x ⊤ _ _ 
            {assume h2;
            refine ⊤ᵢ}
            {assume h2;
            refine h1}}
        {assume h2;
        refine ind_eq h2 (λ z, z) ⊤ᵢ}
end;

opaque symbol posPropNegEq x: (π (x = (¬ ((¬ x) = ⊤))))≔
begin
    assume x;
    refine propExt x (¬ ((¬ x) = ⊤)) _ _
    {assume h1 h2;
    refine ((ind_eq h2 (λ z, z)) ⊤ᵢ) h1}
    {assume h1;
        refine ∨ₑ [x] [¬ x] [x] (em x) _ _
            {assume h2;
            refine h2}
            {assume h2;
            have H1: π((¬ x) = ⊤)
                {refine propExt (¬ x) ⊤ _ _
                    {assume h3;
                    refine ⊤ᵢ}
                    {assume h3;
                    refine h2}};
            refine ⊥ₑ (h1 H1)}}
end;

opaque symbol negPropPosEq x: (π ((¬ x) = ((¬ x) = ⊤)))≔
begin
    assume x;
    refine propExt (¬ x) ((¬ x) = ⊤) _ _
        {assume h1;
        refine propExt (¬ x) ⊤ _ _ 
            {assume h2;
            refine ⊤ᵢ}
            {assume h2;
            refine h1}}
        {assume h1;
        have H1: π((¬ x) = ⊤) → π(¬ x)
            {assume h2;
            refine (ind_eq h2 (λ z, z)) ⊤ᵢ};
        refine H1 h1}
end;

opaque symbol negPropNegEq x: (π ((¬ x) = (¬ (x = ⊤))))≔
begin
    assume x;
    refine propExt (¬ x) (¬ (x = ⊤)) _ _
        {assume h1 h2;
        refine h1 (ind_eq h2 (λ z, z) ⊤ᵢ)}
        {assume h1 h2;
        have H1: π(x = ⊤)
            {refine propExt x ⊤ _ _
                {assume h3;
                refine ⊤ᵢ}
                {assume h3;
                refine h2}};
        refine h1 H1}
end;

opaque symbol negEqPosProp x: (π ((¬ ((¬ x) = ⊤)) = x))≔
begin
    assume x;
    symmetry;
    refine propExt x (¬ ((¬ x) = ⊤)) _ _
    {assume h1 h2;
    refine ((ind_eq h2 (λ z, z)) ⊤ᵢ) h1}
    {assume h1;
        refine ∨ₑ (em x) _ _ 
            {assume h2;
            refine h2}
            {assume h2;
            have H1: π((¬ x) = ⊤)
                {refine propExt (¬ x) ⊤ _ _
                    {assume h3;
                    refine ⊤ᵢ}
                    {assume h3;
                    refine h2}};
            refine ⊥ₑ (h1 H1)}}
end;

opaque symbol negEqNegProp x: (π ((¬ (x = ⊤)) = (¬ x)))≔
begin
    assume x;
    symmetry;
    refine propExt (¬ x) (¬ (x = ⊤)) _ _
        {assume h1 h2;
        refine h1 (ind_eq h2 (λ z, z) ⊤ᵢ)}
        {assume h1 h2;
        have H1: π(x = ⊤)
            {refine propExt x ⊤ _ _
                {assume h3;
                refine ⊤ᵢ}
                {assume h3;
                refine h2}};
        refine h1 H1}
end;

opaque symbol posEqPosProp x: (π ((x = ⊤) = x))≔
begin
    assume x;
    symmetry;
    refine propExt x (x = ⊤) _ _
        {assume h1;
        refine propExt x ⊤ _ _ 
            {assume h2;
            refine ⊤ᵢ}
            {assume h2;
            refine h1}}
        {assume h2;
        refine (ind_eq h2 (λ z, z)) ⊤ᵢ}
end;

opaque symbol posEqNegProp x: (π (((¬ x) = ⊤) = (¬ x)))≔
begin
    assume x;
    symmetry;
    refine propExt (¬ x) ((¬ x) = ⊤) _ _
        {assume h1;
        refine propExt (¬ x) ⊤ _ _ 
            {assume h2;
            refine ⊤ᵢ}
            {assume h2;
            refine h1}}
        {assume h1;
        have H1: π((¬ x) = ⊤) → π(¬ x)
            {assume h2;
            refine (ind_eq  h2 (λ z, z)) ⊤ᵢ};
        refine H1 h1}
end;


////////// Transformations involving ⊤ and ⊥

opaque symbol topPosProp x: (π (( ⊤ = x) = x))≔ 
begin
    assume x;
    refine propExt (⊤ = x) x _ _
        {assume h1;
        have H1 : π x → π x
            {assume h2;
            refine h2};
        refine (ind_eq h1 (λ z, z ⇒ x) H1) ⊤ᵢ}
        {assume h1;
        refine propExt ⊤ x _ _
            {assume h2;
            refine h1}
            {assume h2;
            refine ⊤ᵢ}}
end;

opaque symbol botNegProp x: (π ((⊥ = x) = (¬ x)))≔ 
begin
    assume x;
    refine propExt (⊥ = x) (¬ x) _ _
        {assume h1;
        have H1 : π x → π x
            {assume h2;
            refine h2};
        refine ind_eq h1 (λ z, x ⇒ z) H1}
        {assume h1;
        refine propExt ⊥ x _ _
            {assume h2;
            refine ⊥ₑ h2}
            {assume h2;
            refine h1 h2}}
end;

opaque symbol negPropEqBot x: (π ((¬ x) = (x = ⊥)))≔ 
begin
    assume x;
    type propExt (¬ x) (x = ⊥) _ _;
    refine propExt (¬ x) (x = ⊥) _ _
        {assume h1;
        refine propExt x ⊥ _ _
        {assume h2;
            refine h1 h2}
        {assume h2;
            refine ⊥ₑ h2}}
        {assume h1;
        refine ind_eq h1 (λ y, ¬ y) (λ h : π ⊥, h)}
end;

opaque symbol negPropNegEqBot x: π (¬ x = ¬ (¬ x = ⊥))≔ 
begin
    assume x;
    refine propExt (¬ x) (¬ (¬ x = ⊥)) _ _
        {assume h1 h2;
        have H1: π (⊥ = ¬ x)
            {symmetry;
            refine h2};
        refine ind_eq H1 (λ y, y) h1}
            {assume h1 h2;
            refine h1 _;
            refine propExt (¬ x) ⊥ _ _
                {assume h3;
                refine h3 h2}
                {assume h3;
                refine ⊥ₑ h3}}
end;

opaque symbol propNegEqBot x: π (x = ¬ (x = ⊥))≔ 
begin
    assume x;
    refine propExt x (¬ (x = ⊥)) _ _
    {assume h1 h2;
    refine ind_eq (h2) (λ z, z ⇒ ⊥) (λ y : π (⊥), y) h1}
    {assume h1;
    refine ¬¬ₑ (x) _;
    assume h2;
    have H1: π (x = ⊥)
        {refine propExt x ⊥ _ _
        {assume h3;
        refine h2 h3}
        {assume h3;
        refine ⊥ₑ h3}};
        refine h1 H1}
end;

opaque symbol PropEqBot x: π (x = (¬ x = ⊥))≔ 
begin
    assume x;
    refine propExt x (¬ x = ⊥) _ _
        {assume h1;
        refine propExt (¬ x) ⊥ _ _
            {assume h2;
            refine h2 h1}
            {assume h2;
            refine ⊥ₑ h2}}
        {assume h1;
        refine ¬¬ₑ x (ind_eq h1 (λ y, ¬ y) (λ h : π ⊥, h))}
end;



////////// Changing Order within Equality Literals

opaque symbol eqSym [T] (x y : τ T) : π((x = y) = (y = x))≔
begin
    assume T x y;
    have H1: π(x = y) → π(y = x)
        {assume h;
        symmetry;
        refine h};
    have H2: π(y = x) → π(x = y)
        {assume h;
        symmetry;
        refine h};
    refine propExt (x = y) (y = x) H1 H2
end;

opaque symbol eqSym_p : Π T: Set, Π x: τ T, Π y: τ T, π (x = y) → π (y = x) ≔
λ T x y h1, ((ind_eq h1 (λ z, y = z)) (eq_refl y));

opaque symbol eqSym_n : Π T: Set, Π x: τ T, Π y: τ T, π (¬ (x = y)) → π (¬ (y = x))≔
// (λ T x y h1, ¬I (y = x) (λ h2, ¬E (x = y) ((λ h3, (=def [T] y x h3) (λ z, x = z) (=ref [T] x)) h2) h1));
(λ T x y h1, (λ h2, h1 ((λ h3, (ind_eq h3) (λ z, x = z) (eq_refl [T] x)) h2)));


////////// Implicit transformations marked as calculus rule applications by Leo-III

symbol polaritySwitchEqLit a b : π ((a = b) = ((¬ a) = (¬ b)))≔
begin
    assume a b;
    refine propExt (a = b) (¬ a = ¬ b) _ _ 
        {assume h1;
        have H1: π (b = a)
                {symmetry;
                refine h1};
        refine propExt (¬ a) (¬ b) _ _
            {assume h2;
            refine ind_eq H1 (λ x, ¬ x) h2}
            {assume h2;
            refine ind_eq h1 (λ x, ¬ x) h2}}
        {assume h1;
        have H1: π (¬ b = ¬ a)
                {symmetry;
                refine h1};
        refine propExt a b _ _
            {assume h2;
            have H2: π (¬ (¬ a))
                {assume h3;
                refine h3 h2};
            refine (¬¬ₑ b) (ind_eq H1 (λ x, (¬ x)) H2)}
            {assume h2;
            have H2: π (¬ (¬ b))
                {assume h3;
                refine h3 h2};
            refine (¬¬ₑ a) (ind_eq h1 (λ x, (¬ x)) H2)}}
end;

symbol lifteq_t_n [a] (x y : τ a) : π ((x ≠ y) = (¬ (x = y)))≔
begin
    assume a x y;
	reflexivity
end;