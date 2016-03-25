module Data.Fin.Extra where

open import Data.Nat
    renaming (suc to S; zero to Z; _+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Fin

open import Function
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

inject-1 : ∀ {n} → (i : Fin (S n)) → toℕ i ≢ n → Fin n
inject-1 {Z}   zero    p = contradiction refl p
inject-1 {Z}   (suc i) p = i
inject-1 {S n} zero    p = zero
inject-1 {S n} (suc i) p = suc (inject-1 i (p ∘ cong S))
