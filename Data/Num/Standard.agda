module Data.Num.Standard where
-- Standard positional notations

open import Data.Nat
open ≤-Reasoning
    renaming (begin_ to start_; _∎ to _□)
 -- using (≰⇒>; +-∸-assoc; ∸-mono)
open import Data.Nat.Properties
open import Data.Fin using (Fin)
    renaming (zero to Fzero; suc to Fsuc; toℕ to F→N; fromℕ≤ to N→F)
open import Data.Fin.Properties using (bounded)
open import Function
open import Relation.Nullary
-- open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse; fromWitness; fromWitnessFalse)

open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; sym; trans; inspect)
open PropEq.≡-Reasoning
open import Relation.Binary

ℕ-isDecTotalOrder   = DecTotalOrder.isDecTotalOrder decTotalOrder
ℕ-isTotalOrder      = IsDecTotalOrder.isTotalOrder ℕ-isDecTotalOrder
ℕ-isPartialOrder    = IsTotalOrder.isPartialOrder ℕ-isTotalOrder
ℕ-isPreorder        = IsPartialOrder.isPreorder ℕ-isPartialOrder
≤-refl      = IsPreorder.reflexive ℕ-isPreorder
≤-antisym   = IsPartialOrder.antisym ℕ-isPartialOrder
≤-total     = IsTotalOrder.total ℕ-isTotalOrder


data Digit : (base : ℕ) → Set where
    D : ∀ {base} → Fin base → Digit base

infixl 6 _D+_

_D+_ : ∀ {b} → Digit b → Digit b → Digit b
D x D+ D {b} y with b ≤? (F→N x + F→N y)
D x D+ D {b} y | yes p = D $ N→F {F→N x + F→N y ∸ b} $
    start
        suc (F→N x + F→N y ∸ b)
    ≤⟨ ≤-refl (sym (+-∸-assoc 1 p)) ⟩
        (suc (F→N x) + F→N y) ∸ b
    ≤⟨ ∸-mono {suc (F→N x) + F→N y} {b + b} {b} {b} (bounded x +-mono (
            start
                F→N y
            ≤⟨ n≤1+n (F→N y) ⟩
                suc (F→N y)
            ≤⟨ bounded y ⟩
                b
            □
        )) (≤-refl refl) ⟩
        b + b ∸ b
    ≤⟨ ≤-refl (m+n∸n≡m b b) ⟩
        b
    □
D x D+ D {b} y | no ¬p = D $ N→F (≰⇒> ¬p)

-- start
--     {!   !}
-- ≤⟨ {!    !} ⟩
--     {!    !}
-- ≤⟨ {!    !} ⟩
--     {!   !}
-- ≤⟨ {!    !} ⟩
--     {!   !}
-- ≤⟨ {!    !} ⟩
--     {!   !}
-- □

-- begin
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ∎
