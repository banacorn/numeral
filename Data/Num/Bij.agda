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

infixl 7 _*B_
infixl 6 _+B_

data DigitB : Set where
    one : DigitB
    two : DigitB

Bij : Set
Bij = List DigitB

incrB : Bij → Bij
incrB []        = one ∷ []
incrB (one ∷ a) = two ∷ a
incrB (two ∷ a) = one ∷ incrB a

-- addition
_+B_ : Bij → Bij → Bij
[]         +B b        = b
a          +B []       = a
(one ∷ as) +B (one ∷ bs) = two ∷ as +B bs
(one ∷ as) +B (two ∷ bs) = one ∷ incrB (as +B bs)
(two ∷ as) +B (one ∷ bs) = one ∷ incrB (as +B bs)
(two ∷ as) +B (two ∷ bs) = two ∷ incrB (as +B bs)

-- arithmetic shift
*2_ : Bij → Bij
*2 []         = []
*2 (one ∷ as) = two ∷ *2 as
*2 (two ∷ as) = two ∷ incrB (*2 as)

-- multiplication
_*B_ : Bij → Bij → Bij
[]         *B b = []
(one ∷ as) *B b =      b +B (*2 (as *B b))
(two ∷ as) *B b = b +B b +B (*2 (as *B b))

--------------------------------------------------------------------------------
-- Ordering
--------------------------------------------------------------------------------

infix 4 _≤-digitB_ _≤B_ _<B_

data _≤-digitB_ : Rel DigitB Level.zero where
    1≤1 : one ≤-digitB one
    1≤2 : one ≤-digitB two
    2≤2 : two ≤-digitB two

data _≤B_ : Rel Bij Level.zero where
    []≤all : ∀ {n} → [] ≤B n
    ≤here : ∀ {as bs a b}           -- compare the least digit
            → {a≤b : a ≤-digitB b}
            → {as≡bs : as ≡ bs}
            → a ∷ as ≤B b ∷ bs
    ≤there : ∀ {as bs a b}
             → (as<bs : incrB as ≤B bs) -- compare the rest digits
             → a ∷ as ≤B b ∷ bs

_<B_ : Rel Bij Level.zero
a <B b = incrB a ≤B b


{-


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
        -- split morphism
        -- !_! is a section of [_]
        -- [_] is a retraction of !_!
        [!!]-id : ∀ n → [ ! n ! ] ≡ n

[_] : ∀ {t} → {{convT : Conversion t}} → t → Bij
[_] {{convT}} = Conversion.[ convT ]

!_! : ∀ {t} → {{convT : Conversion t}} → Bij → t
!_! {{convT}} = Conversion.! convT !

[!!]-id : ∀ {t} → {{convT : Conversion t}} → (n : Bij) → [ ! n ! ] ≡ n
[!!]-id {{convT}} = Conversion.[!!]-id convT
