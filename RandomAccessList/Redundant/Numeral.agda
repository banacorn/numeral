module RandomAccessList.Redundant.Numeral where

--  Base: 2
--  Digit: { 0, 1, 2 }
--
--  Numeral System which supports efficient addition, substraction
--  and arithmetic shift.

open import Data.List

--------------------------------------------------------------------------------
--  Digits
--------------------------------------------------------------------------------

data Digit : Set where
    zero : Digit
    one : Digit
    two : Digit

-- add
_⊕_ : Digit → Digit → Digit
zero ⊕ y    = y
x    ⊕ zero = x
one  ⊕ one  = two
one  ⊕ two  = zero
two  ⊕ one  = zero
two  ⊕ two  = one

-- complement
¬_ : Digit → Digit
¬ zero = zero
¬ one = two
¬ two = one

-- carry
_⊙_ : Digit → Digit → Digit
one ⊙ two = one
two ⊙ one = one
two ⊙ two = one
_   ⊙ _   = zero

--------------------------------------------------------------------------------
--  Sequence of Digits
--------------------------------------------------------------------------------

Redundant : Set
Redundant = List Digit

incr : Redundant → Redundant
incr [] = one ∷ []
incr (zero ∷ xs) = one ∷ xs
incr (one ∷ xs) = two ∷ xs
incr (two ∷ xs) = zero ∷ incr xs

decr : Redundant → Redundant
decr [] = []
decr (zero ∷ xs) = two ∷ decr xs
decr (one ∷ xs) = zero ∷ xs
decr (two ∷ xs) = one ∷ xs

_+_ : Redundant → Redundant → Redundant
[] + ys = ys
xs + [] = xs
(x ∷ xs) + (y ∷ ys) = x ⊕ y ∷ (x ⊙ y ∷ []) + (xs + ys)

_─_ : Redundant → Redundant → Redundant
[] ─ ys = []
xs ─ [] = xs
(x ∷ xs) ─ (y ∷ ys) = (x ⊕ ¬ y) ∷ (xs ─ ys) ─ (x ⊙ ¬ y ∷ [])

mul2 : Redundant → Redundant
mul2 [] = []
mul2 (x ∷ xs) = zero ∷ x ∷ xs

div2 : Redundant → Redundant
div2 [] = []
div2 (x ∷ xs) = xs
