module Sandbox.Desc where
-- Ornamental Algebras, Algebraic Ornaments
-- CONOR McBRIDE
-- https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf

open import Data.Product using (_×_; Σ; _,_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

-- a 2 element enumeration to act as a set of tags
data NatTag : Set where
    z : NatTag
    s : NatTag

data BoolTag : Set where
    true : BoolTag
    false : BoolTag

module Plain where
    data PlainDesc : Set₁ where
        arg : (A : Set) → (A → PlainDesc) → PlainDesc   -- read field in A; continue, given its value
        rec : PlainDesc → PlainDesc                     -- read a recursive subnode; continue regardless
        ret : PlainDesc                                 -- stop reading

    ⟦_⟧ : PlainDesc → Set → Set
    ⟦ arg A D ⟧ R = Σ A (λ a → ⟦ D a ⟧ R)
    ⟦ rec D   ⟧ R = R × ⟦ D ⟧ R
    ⟦ ret     ⟧ R = ⊤

    data PlainData (D : PlainDesc) : Set where
        ⟨_⟩ : ⟦ D ⟧ (PlainData D) → PlainData D

    -- ------------
    -- NAT
    -- ------------

    NatDesc : PlainDesc
    NatDesc = arg NatTag f
        where   f : NatTag → PlainDesc
                f z = ret
                f s = rec ret

    Nat : Set
    Nat = PlainData NatDesc

    zero : Nat
    zero = ⟨ (z , tt) ⟩

    suc : Nat → Nat
    suc n = ⟨ (s , n , tt) ⟩

    f : NatTag → BoolTag
    f z = true
    f s = false

    map : (NatTag → BoolTag) → ⟦ NatDesc ⟧ NatTag → ⟦ NatDesc ⟧ BoolTag
    map g (z , tt) = {!   !}
    map g (s , n , tt) = n , {!   !}


    -- map : ∀ {X Y} → (D : PlainDesc) → (X → Y) → ⟦ D ⟧ X → ⟦ D ⟧ Y
    -- map (arg A x) f d = {!   !}
    -- map (rec D) f d = {!   !}
    -- map ret f d = {!   !}

module Indexed where
    data Desc (I : Set) : Set₁ where
        arg : (A : Set) → (A → Desc I) → Desc I
        rec : I → Desc I → Desc I
        ret : I → Desc I

    NatDesc : Desc ⊤
    NatDesc = arg NatTag f
        where   f : NatTag → Desc ⊤
                f z = ret tt
                f s = rec tt (ret tt)

    ⟦_⟧ : ∀ {I} → Desc I → (I → Set) → I → Set
    ⟦ arg A D ⟧ R i = Σ A (λ a → ⟦ D a ⟧ R i)
    ⟦ rec h D ⟧ R i = R h × ⟦ D ⟧ R i
    ⟦ ret o   ⟧ R i = o ≡ i

    data Data {I} (D : Desc I) : I → Set where
        ⟨_⟩ : ∀ {i} → ⟦ D ⟧ (Data D) i → Data D i

    Nat : Set
    Nat = Data NatDesc tt

    zero : Nat
    zero = ⟨ z , refl ⟩

    suc : Nat → Nat
    suc n = ⟨ (s , n , refl) ⟩

    VecDesc : Set → Desc Nat
    VecDesc X = arg NatTag f
        where   f : NatTag → Desc Nat
                f z = ret zero
                f s = arg X (λ x → arg Nat (λ n → rec n (ret (suc n))))

    Vec : Set → Nat → Set
    Vec X n = Data (VecDesc X) n

    nil : ∀ {X} → Vec X zero
    nil = ⟨ (z , refl) ⟩

    cons : ∀ {X n} → X → Vec X n → Vec X (suc n)
    cons {n = n} x xs = ⟨ (s , x , n , xs , refl) ⟩

    -- Conor used _⊆_ here
    _⇒_ : ∀ {I} → (I → Set) → (I → Set) → Set
    X ⇒ Y = ∀ i → X i → Y i


    -- map : ∀ {I X Y} → (D : Desc I) → X ⇒ Y → ⟦ D ⟧ X ⇒ ⟦ D ⟧ Y
    -- map : ∀ {I X Y} → (D : Desc I) → (∀ i → X i → Y i) → (∀ i → ⟦ D ⟧ X i → ⟦ D ⟧ Y i)
    -- map : ∀ {I X Y} → (D : Desc I) → _⇒_ {I} X Y → ⟦ D ⟧ X ⇒ ⟦ D ⟧ Y
    -- map (arg A D) f i (a , D') = a , (map (D a) f i D')
    -- map (rec h D) f i (x , D') = f h x , map D f i D'
    -- map (ret o)   f i x        = x
    --
    -- Alg : ∀ {I} → Desc I → (I → Set) → Set
    -- Alg D X = ⟦ D ⟧ X ⇒ X

    -- `fold` won't pass Agda's termination checking if it's defined like this
    --      fold : ∀ {I X} → (D : Desc I) → Alg D X → Data D ⇒ X
    --      fold D φ i ⟨ ds ⟩ = φ i (map D (fold D φ) i ds)
    -- so instead we will fuse map and fold first
    --      fold D φ i ⟨ ds ⟩   = φ i (map D (fold D φ) i ds)
    --                          = φ i (mapFold D D φ i x)
    --      mapFold F G φ i x   = map F (fold G φ) i x
    --                          = map F (λ i d → fold G φ i d) i x
    --                          = map F (λ i d → fold G φ i d) i x
    --                          = map F (φ i (mapFold F G φ)) i x

    -- mapFold : ∀ {I X} → (D E : Desc I) → Alg D X → I → Data D → E
    -- mapFold F G φ i x = map F (φ i (mapFold F G φ)) i x
