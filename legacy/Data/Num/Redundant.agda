module Data.Num.Redundant where

--  Base: 2
--  Digit: { 0, 1, 2 }
--
--  Numeral System which maxports efficient addition, substraction
--  and arithmetic shift.

open import Data.List using (List ; []; _∷_) public
open import Data.Nat renaming (_+_ to _+ℕ_; _<_ to _<ℕ_)
open import Data.Num.Bij

open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_)
import Level
open PropEq.≡-Reasoning

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
-- instances of Conversion, so that we can convert Redundant to B
--------------------------------------------------------------------------------

instance convRedundant : Conversion Redundant
convRedundant = conversion [_]' !_!' [!!]-id'
    where   [_]' : Redundant → Bij
            [     [] ]' = []
            [ zero ∷ xs ]' =    *2 [ xs ]'
            [ one  ∷ xs ]' = one ∷ [ xs ]'
            [ two  ∷ xs ]' = two ∷ [ xs ]'

            !_!' : Bij → Redundant
            ! []     !' = []
            ! one ∷ xs !' = one ∷ ! xs !'
            ! two ∷ xs !' = two ∷ ! xs !'

            [!!]-id' : ∀ xs → [ ! xs !' ]' ≡ xs
            [!!]-id' [] = PropEq.refl
            [!!]-id' (one ∷ xs) = PropEq.cong (λ x → one ∷ x) ([!!]-id' xs)
            [!!]-id' (two ∷ xs) = PropEq.cong (λ x → two ∷ x) ([!!]-id' xs)

--------------------------------------------------------------------------------
--  Equivalence relation
--------------------------------------------------------------------------------

infix 4 _≈_ _≉_

data _≈_ (a b : Redundant) : Set where
    eq : ([a]≡[b] : [ a ] ≡ [ b ]) → a ≈ b

-- the inverse of `eq`
to≡ : ∀ {a b} → a ≈ b → [ a ] ≡ [ b ]
to≡ (eq x) = x

_≉_ : (a b : Redundant) → Set
a ≉ b = a ≈ b → ⊥

-- decidable
{-
_≈?_ : Decidable {A = Redundant} _≈_
a ≈? b with [ a ] ≟ [ b ]
a ≈? b | yes p = yes (eq p)
a ≈? b | no ¬p = no (contraposition to≡ ¬p)
-}

--------------------------------------------------------------------------------
--  Ordering
--------------------------------------------------------------------------------

infix 4 _≲_ _<_
data _≲_ : Rel Redundant Level.zero where
    le : ∀ {a b} ([a]≤[b] : [ a ] ≤B [ b ]) → a ≲ b

-- the inverse of `le`
to≤ : ∀ {a b} → a ≲ b → [ a ] ≤B [ b ]
to≤ (le [a]≤B[b]) = [a]≤B[b]

_<_ : Rel Redundant Level.zero
a < b = incr one a ≲ b

{-
-- decidable
_≲?_ : Decidable _≲_
a ≲? b with [ a ] ≤? [ b ]
a ≲? b | yes p = yes (le p)
a ≲? b | no ¬p = no (contraposition to≤ ¬p)
-}
