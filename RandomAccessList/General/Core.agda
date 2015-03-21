module RandomAccessList.General.Core where

open import Data.List
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_)

data General (A : Set) : ℕ → ℕ → ℕ → Set where
    [] : ∀ {a b n} → General A a b n
    ∺ : ∀ {v a a' b b' n}
        → Vec A v
        → a ⊓ v ≡ a'
        → b ⊔ b ≡ b'
        → General A a b n
        → General A a' b' n


--------------------------------------------------------------------------------
--  Beispiele
--------------------------------------------------------------------------------
