module RandomAccessList.Redundant.Core where

open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)

open import Data.Nat
open import Data.Nat.Etc

data 0-2-RAL (A : Set) : ℕ → Set where
    []     : ∀ {n}                                                               → 0-2-RAL A n
    0∷     : ∀ {n}                                           → 0-2-RAL A (suc n) → 0-2-RAL A n
    _1∷_   : ∀ {n} → BinaryLeafTree A n                      → 0-2-RAL A (suc n) → 0-2-RAL A n
    _,_2∷_ : ∀ {n} → BinaryLeafTree A n → BinaryLeafTree A n → 0-2-RAL A (suc n) → 0-2-RAL A n

infixr 2 0∷
infixr 2 _1∷_
infixr 2 _,_2∷_

--------------------------------------------------------------------------------
-- to ℕ
--------------------------------------------------------------------------------

⟦_⟧ₙ : ∀ {A n} → 0-2-RAL A n → ℕ
⟦          [] ⟧ₙ = 0
⟦       0∷ xs ⟧ₙ = 0 + 2 * ⟦ xs ⟧ₙ
⟦ x     1∷ xs ⟧ₙ = 1 + 2 * ⟦ xs ⟧ₙ
⟦ x , y 2∷ xs ⟧ₙ = 2 + 2 * ⟦ xs ⟧ₙ

⟦_⟧ : ∀ {n A} → 0-2-RAL A n → ℕ
⟦_⟧ {n} xs = 2 ^ n * ⟦ xs ⟧ₙ
