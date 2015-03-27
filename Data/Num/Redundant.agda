module Data.Num.Redundant where

--  Base: 2
--  Digit: { 0, 1, 2 }
--
--  Numeral System which supports efficient addition, substraction
--  and arithmetic shift.


open import Data.List
-- open import Data.Fin renaming (_+_ to _+Fin_) hiding (toℕ; fromℕ)
open import Data.Nat renaming (_+_ to _+ℕ_)

--------------------------------------------------------------------------------
--  Digits
--------------------------------------------------------------------------------

data Digit : Set where
    zero : Digit
    one : Digit
    two : Digit

-- plus
_⊕_ : Digit → Digit → Digit
zero ⊕ y    = y
x    ⊕ zero = x
one  ⊕ one  = two
one  ⊕ two  = one
two  ⊕ one  = one
two  ⊕ two  = two

-- minus
_⊝_ : Digit → Digit → Digit
zero ⊝ y    = zero
x    ⊝ zero = x
one  ⊝ one  = zero
one  ⊝ two  = one
two  ⊝ one  = one
two  ⊝ two  = zero

-- carry
_⊙_ : Digit → Digit → Digit
one ⊙ two = one
two ⊙ one = one
two ⊙ two = one
_   ⊙ _   = zero

-- borrow
_⊘_ : Digit → Digit → Digit
zero ⊘ one = one
zero ⊘ two = one
one  ⊘ two = one
_    ⊘ _   = zero

--------------------------------------------------------------------------------
--  Sequence of Digits
--------------------------------------------------------------------------------

Redundant : Set
Redundant = List Digit

-- "one-sided"
incr : Digit → Redundant → Redundant
incr x [] = x ∷ []
incr x (y ∷ ys) = x ⊕ y ∷ incr (x ⊙ y) ys

decr : Digit → Redundant → Redundant
decr x [] = []
decr x (y ∷ ys) = x ⊝ y ∷ decr (x ⊘ y) ys

-- "two-sided"
_+_ : Redundant → Redundant → Redundant
[] + ys = ys
xs + [] = xs
(x ∷ xs) + (y ∷ ys) = x ⊕ y ∷ incr (x ⊙ y) (xs + ys)

_─_ : Redundant → Redundant → Redundant
[] ─ ys = []
xs ─ [] = xs
(x ∷ xs) ─ (y ∷ ys) = x ⊝ y ∷ decr (x ⊘ y) (xs ─ ys)

-- arithmetic shift
mul2 : Redundant → Redundant
mul2 [] = []
mul2 (x ∷ xs) = zero ∷ x ∷ xs

div2 : Redundant → Redundant
div2 [] = []
div2 (x ∷ xs) = xs

--------------------------------------------------------------------------------
--  Conversions
--------------------------------------------------------------------------------

-- O(lgn)
toℕ : Redundant → ℕ
toℕ []          = 0
toℕ (zero ∷ xs) = 0 +ℕ 2 * toℕ xs
toℕ (one  ∷ xs) = 1 +ℕ 2 * toℕ xs
toℕ (two  ∷ xs) = 2 +ℕ 2 * toℕ xs

-- O(n)
fromℕ : ℕ → Redundant
fromℕ zero = zero ∷ []
fromℕ (suc n) = incr one (fromℕ n)
