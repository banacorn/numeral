module RandomAccessList.General.Redundant where

open import RandomAccessList.General.Core

open import Data.Nat

Redundant : Set → ℕ → Set
Redundant A = General A 0 2

cons : ∀ {n A} → A → Redundant A n → Redundant A n
cons a [] = ?
cons a (∺ x x₁ x₂ xs) = ?
