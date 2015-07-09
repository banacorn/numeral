module RandomAccessList.Standard.Core where

open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)

open import Data.Nat
open import Data.Nat.Etc

--  parameterized by the level of the least significant digit
data 0-1-RAL (A : Set) : ℕ → Set where
    []   : ∀ {n} →                                          0-1-RAL A n
    0∷_  : ∀ {n} →                      0-1-RAL A (suc n) → 0-1-RAL A n
    _1∷_ : ∀ {n} → BinaryLeafTree A n → 0-1-RAL A (suc n) → 0-1-RAL A n

--------------------------------------------------------------------------------
-- to ℕ

⟦_⟧ₙ : ∀ {A n} → 0-1-RAL A n → ℕ
⟦      [] ⟧ₙ = 0
⟦   0∷ xs ⟧ₙ =     2 * ⟦ xs ⟧ₙ
⟦ x 1∷ xs ⟧ₙ = 1 + 2 * ⟦ xs ⟧ₙ

⟦_⟧ : ∀ {n A} → 0-1-RAL A n → ℕ
⟦_⟧ {n} xs = (2 ^ n) * ⟦ xs ⟧ₙ
