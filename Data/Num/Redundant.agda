module Data.Num.Redundant where

--  Base: 2
--  Digit: { 0, 1, 2 }
--
--  Numeral System which supports efficient addition, substraction
--  and arithmetic shift.

open import Data.List using (List ; []; _∷_) public
open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Num.Nat
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_)
    renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
import Level

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
-- instances of Nat, so that we can convert then to ℕ
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

--------------------------------------------------------------------------------
--  Equivalence relation
--------------------------------------------------------------------------------

infix 4 _≈_ _≉_
data _≈_ (a b : Redundant) : Set where
    eq : [ a ] ≡ [ b ] → a ≈ b

-- the inverse of `eq`
to≡ : ∀ {a b} → a ≈ b → [ a ] ≡ [ b ]
to≡ (eq x) = x

_≉_ : (a b : Redundant) → Set
a ≉ b = a ≈ b → ⊥

-- ≈ be setoid
≈-Setoid : Setoid _ _
≈-Setoid = record
    {   Carrier = Redundant
    ;   _≈_ = _≈_
    ;   isEquivalence = record
        {   refl = ≈-refl
        ;   sym = ≈-sym
        ;   trans = ≈-trans
        }
    }
    where
        ≈-refl : Reflexive _≈_
        ≈-refl = eq ≡-refl

        ≈-sym : Symmetric _≈_
        ≈-sym (eq a≈b) = eq (≡-sym a≈b)

        ≈-trans : Transitive _≈_
        ≈-trans (eq a≈b) (eq b≈c) = eq (≡-trans a≈b b≈c)

-- decidable equivalence relation
infix 4 _≈?_
_≈?_ : Decidable {A = Redundant} _≈_
a ≈? b with [ a ] ≟ [ b ]
a ≈? b | yes p = yes (eq p)
a ≈? b | no ¬p = no (contraposition to≡ ¬p)


--------------------------------------------------------------------------------
-- ≲
--------------------------------------------------------------------------------

data _≲_ : Rel Redundant Level.zero where
    le : ∀ {a b} ([a]≤[b] : [ a ] ≤ [ b ]) → a ≲ b

to≤ : ∀ {a b} → a ≲ b → [ a ] ≤ [ b ]
to≤ (le [a]≤[b]) = [a]≤[b]

_≲?_ : Decidable _≲_
a ≲? b with [ a ] ≤? [ b ]
a ≲? b | yes p = yes (le p)
a ≲? b | no ¬p = no (contraposition to≤ ¬p)

≲-decTotalOrder : DecTotalOrder _ _ _
≲-decTotalOrder = record
    {   Carrier = Redundant
    ;   _≈_ = _≈_
    ;   _≤_ = _≲_
    ;   isDecTotalOrder = record
            {   isTotalOrder = record
                    {   isPartialOrder = record
                            {   isPreorder = record
                                    {   isEquivalence = Setoid.isEquivalence ≈-Setoid
                                    ;   reflexive     = ≲-refl
                                    ;   trans         = ≲-trans
                                    }
                            ;   antisym = antisym
                            }
                    ;   total = total
                    }
            ;   _≟_ = _≈?_
            ;   _≤?_ = _≲?_
            }
    }
    where

        ℕ-isDecTotalOrder = DecTotalOrder.isDecTotalOrder decTotalOrder
        ℕ-isTotalOrder = IsDecTotalOrder.isTotalOrder ℕ-isDecTotalOrder
        ℕ-total = IsTotalOrder.total ℕ-isTotalOrder
        ℕ-isPartialOrder = IsTotalOrder.isPartialOrder ℕ-isTotalOrder
        ℕ-antisym =  IsPartialOrder.antisym ℕ-isPartialOrder
        ℕ-isPreorder = IsPartialOrder.isPreorder ℕ-isPartialOrder
        ℕ-isEquivalence = IsPreorder.isEquivalence ℕ-isPreorder
        ℕ-reflexive = IsPreorder.reflexive ℕ-isPreorder
        ℕ-trans = IsPreorder.trans ℕ-isPreorder

        ≲-refl : _≈_ ⇒ _≲_
        ≲-refl (eq [x]≡[y]) = le (ℕ-reflexive [x]≡[y])

        ≲-trans : Transitive _≲_
        ≲-trans (le [a]≤[b]) (le [b]≤[c]) = le (ℕ-trans [a]≤[b] [b]≤[c])

        antisym : Antisymmetric _≈_ _≲_
        antisym (le [x]≤[y]) (le [y]≤[x]) = eq (ℕ-antisym [x]≤[y] [y]≤[x])

        total : Total _≲_
        total x y with ℕ-total [ x ] [ y ]
        total x y | inj₁ [x]≤[y] = inj₁ (le [x]≤[y])
        total x y | inj₂ [y]≤[x] = inj₂ (le [y]≤[x])
