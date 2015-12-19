module Sandbox.IndRec where
-- Ornamental Algebras, Algebraic Ornaments, CONOR McBRIDE
-- https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf
-- A Finite Axiomtization of Inductive-Recursion definitions, Peter Dybjer, Anton Setzer
-- http://www.cse.chalmers.se/~peterd/papers/Finite_IR.pdf

open import Data.Product using (_×_; Σ; _,_)
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

module Plain where
    data Desc : Set₁ where
        arg : (A : Set)             -- a bag of tags to choose constructors with
            → (A → Desc)            -- given a tag, return the description of the constructor it corresponds to
            → Desc
        rec : Desc → Desc           -- recursive subnode
        ret : Desc                  -- stop


    ⟦_⟧ : Desc → Set → Set
    ⟦ arg A D ⟧ R = Σ A (λ a → ⟦ D a ⟧ R)
    ⟦ rec D   ⟧ R = R × ⟦ D ⟧ R
    ⟦ ret     ⟧ R = ⊤

    data Data (D : Desc) : Set where
        ⟨_⟩ : ⟦ D ⟧ (Data D) → Data D

    -- ℕ
    ℕDesc : Desc
    ℕDesc = arg Bool λ { false → ret ; true → rec ret }

    ℕ : Set
    ℕ = Data ℕDesc

    zero : ℕ
    zero = ⟨ (false , tt) ⟩

    suc : ℕ → ℕ
    suc n = ⟨ (true , (n , tt)) ⟩

    -- induction principle on ℕ
    indℕ : (P : ℕ → Set)
         → (P zero)
         → ((n : ℕ) → (P n) → (P (suc n)))
         → (x : ℕ)
         → P x
    indℕ P base step ⟨ true , n-1 , _ ⟩ = step n-1 (indℕ P base step n-1)
    indℕ P base step ⟨ false , _ ⟩ = base

    _+_ : ℕ → ℕ → ℕ
    x + y = indℕ (λ _ → ℕ) y (λ n x → suc x) x

    -- Maybe
    MaybeDesc : Set → Desc
    MaybeDesc A = arg Bool (λ { false → ret ; true → arg A (λ x → ret) })

    Maybe : Set → Set
    Maybe A = Data (MaybeDesc A)

    nothing : ∀ {A} → Maybe A
    nothing = ⟨ (false , tt) ⟩

    just : ∀ {A} → A → Maybe A
    just a = ⟨ (true , (a , tt)) ⟩

    mapMaybe : ∀ {A B} → (A → B) → Maybe A → Maybe B
    mapMaybe f ⟨ true , a , tt ⟩ = ⟨ (true , ((f a) , tt)) ⟩
    mapMaybe f ⟨ false , tt ⟩ = ⟨ false , tt ⟩

    -- List
    ListDesc : Set → Desc
    ListDesc A = arg Bool (λ { false → ret ; true → arg A (λ _ → rec ret )})

    List : Set → Set
    List A = Data (ListDesc A)

    nil : ∀ {A} → List A
    nil = ⟨ (false , tt) ⟩

    cons : ∀ {A} → A → List A → List A
    cons x xs = ⟨ (true , (x , (xs , tt))) ⟩

    mapList : ∀ {A B} → (A → B) → List A → List B
    mapList f ⟨ true , x , xs , tt ⟩ = ⟨ (true , ((f x) , ((mapList f xs) , tt))) ⟩
    mapList f ⟨ false , tt ⟩ = ⟨ false , tt ⟩

    indList : ∀ {A} (P : List A → Set)
            → P nil
            → ((x : A) → (xs : List A) → P xs → P (cons x xs))
            → (xs : List A)
            → P xs
    indList P base step ⟨ true , x , xs , tt ⟩ = step x xs (indList P base step xs)
    indList P base step ⟨ false , tt ⟩ = base

    foldList : ∀ {A B} (f : A → B → B) → B → List A → B
    foldList {A} {B} f e xs = indList (λ _ → B) e (λ x _ acc → f x acc) xs


module Indexed where
    data Desc (I : Set) : Set₁ where
        arg : (A : Set) → (A → Desc I) → Desc I
        rec : I → Desc I → Desc I
        ret : I → Desc I

    ⟦_⟧ : ∀ {I} → Desc I → (I → Set) → (I → Set)
    ⟦ arg A D ⟧ R I = Σ A (λ a → ⟦ D a ⟧ R I)
    ⟦ rec J D ⟧ R I = R I × ⟦ D ⟧ R I
    ⟦ ret J   ⟧ R I = J ≡ I

    data Data {I} (D : Desc I) : I → Set where
        ⟨_⟩ : ∀ {i} → ⟦ D ⟧ (Data D) i → Data D i


    -- ℕ
    ℕDesc : Desc ⊤
    ℕDesc = arg Bool (λ { true → rec tt (ret tt) ; false → ret tt })

    ℕ : Set
    ℕ = Data ℕDesc tt

    zero : ℕ
    zero = ⟨ (false , refl) ⟩

    suc : ℕ → ℕ
    suc n = ⟨ (true , (n , refl)) ⟩

    -- Maybe
    -- MaybeDesc : (A : Set) → Desc ⊤
    -- MaybeDesc A = arg Bool (λ { true → {!   !} ; false → ret tt })
    --
    -- Maybe : Set → Set
    -- Maybe A = Data (MaybeDesc A) tt
    --
    -- nothing : ∀ {A} → Maybe A
    -- nothing = ⟨ (false , refl) ⟩
    --
    -- just : ∀ {A} → A → Maybe A
    -- just n = ⟨ (true , ⟨ (false , refl) ⟩ , refl) ⟩

--
--     ⟦_⟧ : ∀ {I} → Desc I → (I → Set) → I → Set
--     ⟦ arg A D ⟧ R i = Σ A (λ a → ⟦ D a ⟧ R i)
--     ⟦ rec h D ⟧ R i = R h × ⟦ D ⟧ R i
--     ⟦ ret o   ⟧ R i = o ≡ i
--
--     data Data {I} (D : Desc I) : I → Set where
--         ⟨_⟩ : ∀ {i} → ⟦ D ⟧ (Data D) i → Data D i
--
--     Nat : Set
--     Nat = Data NatDesc tt
--
--     zero : Nat
--     zero = ⟨ z , refl ⟩
--
--     suc : Nat → Nat
--     suc n = ⟨ (s , n , refl) ⟩
--
--     VecDesc : Set → Desc Nat
--     VecDesc X = arg NatTag f
--         where   f : NatTag → Desc Nat
--                 f z = ret zero
--                 f s = arg X (λ x → arg Nat (λ n → rec n (ret (suc n))))
--
--     Vec : Set → Nat → Set
--     Vec X n = Data (VecDesc X) n
--
--     nil : ∀ {X} → Vec X zero
--     nil = ⟨ (z , refl) ⟩
--
--     cons : ∀ {X n} → X → Vec X n → Vec X (suc n)
--     cons {n = n} x xs = ⟨ (s , x , n , xs , refl) ⟩
--
--     -- Conor used _⊆_ here
--     _⇒_ : ∀ {I} → (I → Set) → (I → Set) → Set
--     X ⇒ Y = ∀ i → X i → Y i
--
--
--     -- map : ∀ {I X Y} → (D : Desc I) → X ⇒ Y → ⟦ D ⟧ X ⇒ ⟦ D ⟧ Y
--     -- map : ∀ {I X Y} → (D : Desc I) → (∀ i → X i → Y i) → (∀ i → ⟦ D ⟧ X i → ⟦ D ⟧ Y i)
--     -- map : ∀ {I X Y} → (D : Desc I) → _⇒_ {I} X Y → ⟦ D ⟧ X ⇒ ⟦ D ⟧ Y
--     -- map (arg A D) f i (a , D') = a , (map (D a) f i D')
--     -- map (rec h D) f i (x , D') = f h x , map D f i D'
--     -- map (ret o)   f i x        = x
--     --
--     -- Alg : ∀ {I} → Desc I → (I → Set) → Set
--     -- Alg D X = ⟦ D ⟧ X ⇒ X
--
--     -- `fold` won't pass Agda's termination checking if it's defined like this
--     --      fold : ∀ {I X} → (D : Desc I) → Alg D X → Data D ⇒ X
--     --      fold D φ i ⟨ ds ⟩ = φ i (map D (fold D φ) i ds)
--     -- so instead we will fuse map and fold first
--     --      fold D φ i ⟨ ds ⟩   = φ i (map D (fold D φ) i ds)
--     --                          = φ i (mapFold D D φ i x)
--     --      mapFold F G φ i x   = map F (fold G φ) i x
--     --                          = map F (λ i d → fold G φ i d) i x
--     --                          = map F (λ i d → fold G φ i d) i x
--     --                          = map F (φ i (mapFold F G φ)) i x
--
--     -- mapFold : ∀ {I X} → (D E : Desc I) → Alg D X → I → Data D → E
--     -- mapFold F G φ i x = map F (φ i (mapFold F G φ)) i x
