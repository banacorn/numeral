module Data.Num where

open import Data.Num.Core public
open import Data.Num.Surjection public
open import Data.Num.Injection public
open import Data.Num.Bijection public

open import Data.Nat
open import Data.Nat.Properties.Extra
open import Data.Nat.DM
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Function.Surjection
open import Function.Injection
open import Function.Bijection

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

_⊹_ : ∀ {b d o}
    → {surj : True (Surjective? b d o)}
    → (xs ys : Num b d o)
    → Num b d o
_⊹_ {b} {d} {o}      xs       ys        with Surjective? b d o
_⊹_ {b} {d} {o}      ∙        ∙        | yes surj = ∙
_⊹_ {b} {d} {o}      ∙        (y ∷ ys) | yes surj = y ∷ ys
_⊹_ {b} {d} {o}      (x ∷ xs) ∙        | yes surj = x ∷ xs
_⊹_ {b} {d} {o}      (x ∷ xs) (y ∷ ys) | yes surj with _divMod_ (o + Fin.toℕ x + Fin.toℕ y) b {fromWitnessFalse (>⇒≢ (Surjective⇒b≥1 surj))}
_⊹_ {b} {d} {o}      (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq =
    inject≤ remainder d≥b ∷ n+ quotient (_⊹_ {surj = fromWitness surj} xs ys)
    where   d≥b : d ≥ b
            d≥b = Surjective⇒d≥b surj
_⊹_ {b} {d} {o} {()} xs ys | no ¬surj

BijN : ℕ → Set
BijN b = Num (suc b) (suc b) 1

BijN⇒Surjective : ∀ b → Surjective (Num⟶ℕ (suc b) (suc b) 1)
BijN⇒Surjective b with surjectionView (suc b) (suc b) 1
BijN⇒Surjective b | Surj surjCond = SurjCond⇒Surjective surjCond
BijN⇒Surjective b | NonSurj (Offset≥2 (s≤s ()))
BijN⇒Surjective b | NonSurj (NotEnoughDigits _ d≱b) = contradiction (s≤s ≤-refl) d≱b

BijN⇒Injective : ∀ b → Injective (Num⟶ℕ (suc b) (suc b) 1)
BijN⇒Injective b with injectionView (suc b) (suc b) 1
BijN⇒Injective b | Inj injCond = InjCond⇒Injective injCond
BijN⇒Injective b | NonInj (Redundant d>b) = contradiction refl (>⇒≢ d>b)

BijN⇒Bijective : ∀ b → Bijective (Num⟶ℕ (suc b) (suc b) 1)
BijN⇒Bijective b with bijectionView (suc b) (suc b) 1
BijN⇒Bijective b | Bij surjCond injCond = SurjCond∧InjCond⇒Bijective surjCond injCond
BijN⇒Bijective b | NonSurj (Offset≥2 (s≤s ()))
BijN⇒Bijective b | NonSurj (NotEnoughDigits _ d≱b) = contradiction (s≤s ≤-refl) d≱b
BijN⇒Bijective b | NonInj (Redundant d>b) = contradiction refl (>⇒≢ d>b)
