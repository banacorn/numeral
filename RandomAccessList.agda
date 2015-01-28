module RandomAccessList where

open import BuildingBlock
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)

-- parameterized by the level of the least significant digit
data RandomAccessList (A : Set) : ℕ → Set where
    [] : ∀ {n} → RandomAccessList A n
    0∷_ : ∀ {n} → RandomAccessList A (suc n) → RandomAccessList A n
    _1∷_ : ∀ {n} → BinaryLeafTree A n → RandomAccessList A (suc n) → RandomAccessList A n

toℕ : ∀ {A n} → RandomAccessList A n → ℕ
toℕ [] = zero
toℕ (0∷ xs) = 2 * (toℕ xs)
toℕ (_ 1∷ xs) = 1 + 2 * toℕ xs

Null : ∀ {A n} → RandomAccessList A n → Set
Null [] = ⊤
Null (0∷ xs) = Null xs
Null (x 1∷ xs) = ⊥

incr : ∀ {A n} → BinaryLeafTree A n → RandomAccessList A n → RandomAccessList A n
incr a [] = a 1∷ []
incr a (0∷ xs) = a 1∷ xs
incr a (x 1∷ xs) = 0∷ (incr (Node a x) xs)

--decr : ∀ {A n} → (xs : RandomAccessList A n) → ¬ (Null xs) → RandomAccessList A n
-- decr xs p = {!   !}
