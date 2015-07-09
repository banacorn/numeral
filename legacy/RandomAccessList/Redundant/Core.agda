module RandomAccessList.Redundant.Core where

open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)

open import Data.Num.Redundant
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Etc

infixr 2 0∷ _1∷_ _,_2∷_

data 0-2-RAL (A : Set) : ℕ → Set where
    []     : ∀ {n}                                                               → 0-2-RAL A n
    0∷     : ∀ {n}                                           → 0-2-RAL A (suc n) → 0-2-RAL A n
    _1∷_   : ∀ {n} → BinaryLeafTree A n                      → 0-2-RAL A (suc n) → 0-2-RAL A n
    _,_2∷_ : ∀ {n} → BinaryLeafTree A n → BinaryLeafTree A n → 0-2-RAL A (suc n) → 0-2-RAL A n

--------------------------------------------------------------------------------
-- to Redundant Binary Numeral System
--------------------------------------------------------------------------------

⟦_⟧ₙ : ∀ {n A} → 0-2-RAL A n → Redundant
⟦          [] ⟧ₙ = []
⟦       0∷ xs ⟧ₙ = zero ∷ ⟦ xs ⟧ₙ
⟦ x     1∷ xs ⟧ₙ = one  ∷ ⟦ xs ⟧ₙ
⟦ x , y 2∷ xs ⟧ₙ = two  ∷ ⟦ xs ⟧ₙ

⟦_⟧ : ∀ {n A} → 0-2-RAL A n → Redundant
⟦_⟧ {n} xs = n <<< ⟦ xs ⟧ₙ

--------------------------------------------------------------------------------
-- to ℕ
--------------------------------------------------------------------------------

{-
[_]ₙ : ∀ {A n} → 0-2-RAL A n → ℕ
[          [] ]ₙ = 0
[       0∷ xs ]ₙ = 0 + 2 * [ xs ]ₙ
[ x     1∷ xs ]ₙ = 1 + 2 * [ xs ]ₙ
[ x , y 2∷ xs ]ₙ = 2 + 2 * [ xs ]ₙ

[_] : ∀ {n A} → 0-2-RAL A n → ℕ
[_] {n} xs = 2 ^ n * [ xs ]ₙ
-}
