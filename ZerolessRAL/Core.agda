module ZerolessRAL.Core where

open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)

open import Data.Nat
open import Data.Nat.Etc

--  parameterized by the level of the least significant digit
data 1-2-RAL (A : Set) : ℕ → Set where
    []     : ∀ {n}                                                               → 1-2-RAL A n
    _1∷_   : ∀ {n} → BinaryLeafTree A n                      → 1-2-RAL A (suc n) → 1-2-RAL A n
    _,_2∷_ : ∀ {n} → BinaryLeafTree A n → BinaryLeafTree A n → 1-2-RAL A (suc n) → 1-2-RAL A n

--------------------------------------------------------------------------------
-- to ℕ

⟦_⟧ₙ : ∀ {A n} → 1-2-RAL A n → ℕ
⟦          [] ⟧ₙ = 0
⟦ x     1∷ xs ⟧ₙ = 1 + 2 * ⟦ xs ⟧ₙ
⟦ x , y 2∷ xs ⟧ₙ = 2 + 2 * ⟦ xs ⟧ₙ

⟦_⟧ : ∀ {n A} → 1-2-RAL A n → ℕ
⟦_⟧ {n} xs = 2 ^ n * ⟦ xs ⟧ₙ
