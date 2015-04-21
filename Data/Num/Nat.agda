--------------------------------------------------------------------------------
--  typeclass for converting data types to ℕ
--  http://people.cs.kuleuven.be/~dominique.devriese/agda-instance-arguments/icfp001-Devriese.pdf

module Data.Num.Nat where

open import Data.Nat

record Nat (t : Set) : Set where
    constructor nat
    field
        [_] : t → ℕ
        !_! : ℕ → t

[_] : ∀ {t} → {{natT : Nat t}} → t → ℕ
[_] {{natT}} = Nat.[ natT ]

!_! : ∀ {t} → {{natT : Nat t}} → ℕ → t
!_! {{natT}} = Nat.! natT !
