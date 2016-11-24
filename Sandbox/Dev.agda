module Sandbox.Dev where

-- open import Data.Num.Core
-- open import Data.Num.Bounded
-- open import Data.Num.Maximum
-- open import Data.Num.Next
-- open import Data.Num.Increment
-- open import Data.Num.Continuous
--
open import Data.Nat
-- open import Data.Nat.Properties
-- open import Data.Nat.Properties.Simple
-- open import Data.Nat.Properties.Extra
-- open import Data.Nat.DM
--
open import Data.Fin
--     using (Fin; fromℕ≤; inject≤)
--     renaming (zero to z; suc to s)
--
-- open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)
-- open import Data.Product
-- open import Data.Empty using (⊥)
-- open import Data.Unit using (⊤; tt)
--
-- open import Function
-- open import Relation.Nullary.Decidable
-- open import Relation.Nullary
-- open import Relation.Nullary.Negation
-- open import Relation.Binary
-- open import Relation.Binary.PropositionalEquality
--
-- open ≡-Reasoning
-- open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
-- open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

-- data List (A : Set) : Set where
--     [] : List A
--     _∷_ : A → List A → List A

-- data Vec (A : Set) : ℕ → Set where
--     [] : Vec A 0
--     _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
--
-- open import Data.Bool
--
-- null : ∀ {A n} → Vec A n → Bool
-- null [] = true
-- null (x ∷ xs) = false
--
-- head : ∀ {A n} → Vec A (suc n) → A
-- head (x ∷ xs) = x
--
-- filter : ∀ {A} → (A → Bool) → List A → List A
-- filter f [] = []
-- filter f (x ∷ xs) = {!   !}
--
-- data ⊤ : Set where
--     tt : ⊤
--
-- data ⊥ : Set where
--
-- non-empty : ∀ {A} → List A → Set
-- non-empty []       = ⊥
-- non-empty (x ∷ xs) = ⊤
--
-- head : ∀ {A} → (xs : List A) → non-empty xs → A
-- head []       proof = {!   !}
-- head (x ∷ xs) proof = {!   !}

data Bool : Set where
    False   : Bool
    True    : Bool

¬_ : Bool → Bool
¬ True  = {!   !}
¬ False = {!   !}

two : Fin 3
two = suc zero₂
    where   zero₂ : Fin 2
            zero₂ = zero

z : Fin 3
z = zero
