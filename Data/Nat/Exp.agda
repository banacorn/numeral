module Data.Nat.Exp where

open import Data.Nat

_^_ : ℕ → ℕ → ℕ
a ^ zero  = 1
a ^ suc b = a * (a ^ b)
