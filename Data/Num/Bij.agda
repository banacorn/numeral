module Data.Num.Bij where

open import Data.List hiding ([_])
open import Relation.Binary

open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_)
import Level
--------------------------------------------------------------------------------
-- Bijective Numeration
--
--  A numeral system which has a unique representation for every non-negative
--  interger
--  http://en.wikipedia.org/wiki/Bijective_numeration
--------------------------------------------------------------------------------

-- zeroless binary number

data BijDigit : Set where
    one : BijDigit
    two : BijDigit

-- BijDigit negation
¬_ : BijDigit → BijDigit
¬ one = two
¬ two = one

-- BijDigit addition
_⊕_ : BijDigit → BijDigit → BijDigit
one ⊕ b = ¬ b
two ⊕ b =   b

--------------------------------------------------------------------------------
--  Sequence of BijDigits
--------------------------------------------------------------------------------

Bij : Set
Bij = List BijDigit

incr : Bij → Bij
incr []        = one ∷ []
incr (one ∷ a) = two ∷ a
incr (two ∷ a) = one ∷ incr a


_+_ : Bij → Bij → Bij
[]       + b        = b
a        + []       = a
(one ∷ as) + (one ∷ bs) = two ∷ as + bs                 -- carry : none
(one ∷ as) + (two ∷ bs) = one ∷ incr (as + bs)          -- carry : 1
(two ∷ as) + (one ∷ bs) = one ∷ incr (as + bs)          -- carry : 1
(two ∷ as) + (two ∷ bs) = two ∷ incr (incr (as + bs))   -- carry : 2

*2_ : Bij → Bij
*2 [] = []
*2 (one ∷ as) = two ∷ *2 as
*2 (two ∷ as) = two ∷ incr (*2 as)


infix 4 _≲_

data _≲-digit_ : Rel BijDigit Level.zero where
    1≲1 : one ≲-digit one
    1≲2 : one ≲-digit two
    2≲2 : two ≲-digit two

data _≲_ : Rel Bij Level.zero where
    []≲all : ∀ {n} → [] ≲ n
    ≲here : ∀ {as bs a b}           -- compare the least digit
          → {a≲b : a ≲-digit b}
          → {as≡bs : as ≡ bs}
          → a ∷ as ≲ b ∷ bs
    ≲there : ∀ {as bs a b}
           → (as<bs : incr as ≲ bs) -- compare the rest digits
           → a ∷ as ≲ b ∷ bs

{-

to≤ : ∀ {a b} → a ≲ b → [ a ] ≤ [ b ]
to≤ (le [a]≤[b]) = [a]≤[b]

_<_ : Rel Redundant Level.zero
a < b = incr one a ≲ b



decr : Bij → Bij
decr [] = []
decr (one ∷ a) = a
decr (two ∷ a) = one ∷ a

_-_ : Bij → Bij → Bij
[] - bs = []
as - [] = as
(one ∷ as) - (one ∷ bs) = as - bs
(one ∷ as) - (two ∷ bs) = one ∷ decr (as - bs)
(two ∷ as) - (one ∷ bs) = one ∷ as - bs
(two ∷ as) - (two ∷ bs) = as - bs
-}

--------------------------------------------------------------------------------
--  typeclass for converting data types to Bij
--  http://people.cs.kuleuven.be/~dominique.devriese/agda-instance-arguments/icfp001-Devriese.pdf

record Conversion (t : Set) : Set where
    constructor conversion
    field
        [_] : t   → Bij
        !_! : Bij → t
        [!!]-id : ∀ n → [ ! n ! ] ≡ n

[_] : ∀ {t} → {{convT : Conversion t}} → t → Bij
[_] {{convT}} = Conversion.[ convT ]

!_! : ∀ {t} → {{convT : Conversion t}} → Bij → t
!_! {{convT}} = Conversion.! convT !

[!!]-id : ∀ {t} → {{convT : Conversion t}} → (n : Bij) → [ ! n ! ] ≡ n
[!!]-id {{convT}} = Conversion.[!!]-id convT
