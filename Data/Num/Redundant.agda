module Data.Num.Redundant where

--  Base: 2
--  Digit: { 0, 1, 2 }
--
--  Numeral System which supports efficient addition, substraction
--  and arithmetic shift.

open import Data.List using (List ; []; _∷_) public
open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Num.Nat

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
>> : Redundant → Redundant
>> xs = zero ∷ xs

<< : Redundant → Redundant
<< [] = []
<< (x ∷ xs) = xs

_>>>_ : ℕ → Redundant → Redundant
zero >>> xs = xs
suc n >>> xs = n >>> (>> xs)

_<<<_ : ℕ → Redundant → Redundant
zero  <<< xs = xs
suc n <<< [] = []
suc n <<< (x ∷ xs) = n <<< xs

--------------------------------------------------------------------------------
-- instances of Nat
--------------------------------------------------------------------------------

instance natDigit : Nat Digit
natDigit = nat [_]'
    where   [_]' : Digit → ℕ
            [ zero ]' = 0
            [ one  ]' = 1
            [ two  ]' = 2

instance natRedundant : Nat Redundant
natRedundant = nat [_]'
    where   [_]' : Redundant → ℕ
            [     [] ]' = 0
            [ x ∷ xs ]' = [ x ] +ℕ 2 * [ xs ]'
