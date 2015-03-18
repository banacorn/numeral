module GeneralRAL.Core where

open import Data.List
open import Data.Nat
open import Data.Vec

data General (A : Set) : ℕ → ℕ → ℕ → Set where
    [] : ∀ {n} → General A 0 0 n
    _∺_ : ∀ {v a b n} → Vec A v → General A a b n → General A (a ⊓ v) (b ⊔ v) n


--------------------------------------------------------------------------------
--  Beispiele
--------------------------------------------------------------------------------

RAL : Set → ℕ → Set
RAL A = General A 0 1

Zeroless : Set → ℕ → Set
Zeroless A = General A 1 2

Redundant : Set → ℕ → Set
Redundant A = General A 0 2
