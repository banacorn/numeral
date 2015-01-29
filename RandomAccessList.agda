module RandomAccessList where

open import BuildingBlock
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties using (cancel-*-right)
--open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym)
open PropEq.≡-Reasoning

-- open import Relation.Nullary using (¬_)

-- parameterized by the level of the least significant digit
data RandomAccessList (A : Set) : ℕ → Set where
    [] : ∀ {n} → RandomAccessList A n
    0∷_ : ∀ {n} → RandomAccessList A (suc n) → RandomAccessList A n
    _1∷_ : ∀ {n} → BinaryLeafTree A n → RandomAccessList A (suc n) → RandomAccessList A n

⟦_⟧ : ∀ {A n} → RandomAccessList A n → ℕ
⟦ [] ⟧ = zero
⟦ 0∷ xs ⟧ = 2 * ⟦ xs ⟧
⟦ _ 1∷ xs ⟧ = 1 + 2 * ⟦ xs ⟧

n*a≡0⇒a≡0 : (a n : ℕ) → 0 < n → n * a ≡ 0 → a ≡ 0
n*a≡0⇒a≡0 a       zero    ()        n*a≡0
n*a≡0⇒a≡0 zero    (suc n) (s≤s z≤n) a+n*a≡0 = refl
n*a≡0⇒a≡0 (suc a) (suc n) (s≤s z≤n) ()

Null : ∀ {A n} → (xs : RandomAccessList A n) → Dec (⟦ xs ⟧ ≡ zero)
Null [] = yes refl
Null (0∷ xs) = map′ (cong (λ w → 2 * w)) (n*a≡0⇒a≡0 ⟦ xs ⟧ (suc (suc zero)) (s≤s z≤n)) (Null xs)
Null (x 1∷ xs) = no (λ ())

incr : ∀ {A n} → BinaryLeafTree A n → RandomAccessList A n → RandomAccessList A n
incr a [] = a 1∷ []
incr a (0∷ xs) = a 1∷ xs
incr a (x 1∷ xs) = 0∷ (incr (Node a x) xs)

--decr : ∀ {A n} → (xs : RandomAccessList A n) → ¬ (Null xs) → RandomAccessList A n
-- decr xs p = {!   !}
