module Data.Num.Unary where

open import Data.Unit
open import Data.Empty
open import Data.List
open import Data.Nat renaming (_+_ to _⊹_)

data Digit : Set where
    [1] : Digit

Unary : Set
Unary = List Digit

_⊕_ : Digit → Digit → Digit
[1] ⊕ [1] = [1]

_⊚_ : Digit → Digit → Digit
[1] ⊚ [1] = [1]

add : Digit → Unary → Unary
add [1] [] = [1] ∷ []
add [1] ([1] ∷ xs) = [1] ∷ add [1] xs

_+_ : Unary → Unary → Unary
[] + ys = ys
xs + [] = xs
(x ∷ xs) + (y ∷ ys) = x ⊕ y ∷ add (x ⊚ y) (xs + ys)

_≈_ : Unary → Unary → Set
[] ≈ [] = ⊤
[] ≈ (x ∷ ys) = ⊥
(x ∷ xs) ≈ [] = ⊥
(x ∷ xs) ≈ (y ∷ ys) = xs ≈ ys

fromℕ : ℕ → Unary
fromℕ zero = []
fromℕ (suc n) = fromℕ n

-- fromℕ zero    = []
-- fromℕ (suc n) = [1] ∷ fromℕ n

toℕ : Unary → ℕ
toℕ []       = zero
toℕ (_ ∷ xs) = suc (toℕ xs)
