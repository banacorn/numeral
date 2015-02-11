module RandomAccessList.Core where

open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)

open import Data.Nat

--  parameterized by the level of the least significant digit
data RandomAccessList (A : Set) : ℕ → Set where
    []   : ∀ {n} →                                                   RandomAccessList A n
    0∷_  : ∀ {n} →                      RandomAccessList A (suc n) → RandomAccessList A n
    _1∷_ : ∀ {n} → BinaryLeafTree A n → RandomAccessList A (suc n) → RandomAccessList A n

--------------------------------------------------------------------------------
-- to ℕ

⟦_⟧ₙ : ∀ {A n} → RandomAccessList A n → ℕ
⟦      [] ⟧ₙ = 0
⟦   0∷ xs ⟧ₙ =     2 * ⟦ xs ⟧ₙ
⟦ x 1∷ xs ⟧ₙ = 1 + 2 * ⟦ xs ⟧ₙ

normalize : ∀ {n A} → RandomAccessList A n → RandomAccessList A 0
normalize {zero}  xs = xs
normalize {suc n} xs = normalize (0∷ xs)

⟦_⟧ : ∀ {A n} → RandomAccessList A n → ℕ
⟦_⟧ xs = ⟦ normalize xs ⟧ₙ
