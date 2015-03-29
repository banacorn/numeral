module Data.Num.Redundant.Setoid where

open import Data.Num.Redundant

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_)
    renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

data _~_ (a b : Redundant) : Set where
    eq : (toℕ a ≡ toℕ b) → a ~ b

~-refl : Reflexive _~_
~-refl = eq ≡-refl

~-sym : Symmetric _~_
~-sym (eq a~b) = eq (≡-sym a~b)

~-trans : Transitive _~_
~-trans (eq a~b) (eq b~c) = eq (≡-trans a~b b~c)

isSetoid : Setoid _ _
isSetoid = record {
        Carrier = Redundant
    ;   _≈_ = _~_
    ;   isEquivalence = record {
            refl = ~-refl
        ;   sym = ~-sym
        ;   trans = ~-trans
        }
    }
