require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.HOL Stdlib.Impred Leo-III-lambdapi-lib.extt;

///////////////////////////////////////////////////////////////////////////////////////
////////////////////////////// ACCESSORY RULES ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

////////// Transforming Literals to Their Equational and Non-Equational Forms π 

opaque symbol posPropPosEq_eq x: (π (x = (x = ⊤)))≔
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

opaque symbol posPropPosEq_term : Π x: τ o, π x → π (x = ⊤)
≔ λ x h1, propExt x ⊤ (λ _, ⊤ᵢ) (λ _, h1);

opaque symbol posEqPosProp_term : Π x: Prop, π (x = ⊤) → π x
≔ λ x h2, ind_eq h2 (λ z, z) ⊤ᵢ;

opaque symbol posPropNegEq_eq x: (π (x = (¬ ((¬ x) = ⊤))))≔
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

opaque symbol negPropPosEq_eq x: (π ((¬ x) = ((¬ x) = ⊤)))≔
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


opaque symbol negPropNegEq_eq x: (π ((¬ x) = (¬ (x = ⊤))))≔
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

opaque symbol negEqPosProp_eq x: (π ((¬ ((¬ x) = ⊤)) = x))≔
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


opaque symbol negEqNegProp_eq x: (π ((¬ (x = ⊤)) = (¬ x)))≔
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

opaque symbol posEqNegProp_eq x: (π (((¬ x) = ⊤) = (¬ x)))≔
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

opaque symbol posEqPosProp_eq x: (π ((x = ⊤) = x))≔
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

opaque symbol topPosProp_eq x: (π (( ⊤ = x) = x))≔ 
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

opaque symbol botNegProp_eq x: (π ((⊥ = x) = (¬ x)))≔ 
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


////////// Changing Order within Equality Literals

opaque symbol eqSym_eq [T] (x y : τ T) : π((x = y) = (y = x))≔
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


