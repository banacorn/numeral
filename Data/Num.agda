module Data.Num where

open import Data.Num.Core
open import Data.Num.Surjection

open import Data.Nat
open import Data.Nat.Properties.Extra
open import Data.Nat.DM
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)

open import Relation.Nullary
open import Relation.Nullary.Decidable

_⊹_ : ∀ {b d o} → {surj : True (Surjective? b d o)} → (xs ys : Num b d o) → Num b d o
_⊹_ {b} {d} {o} {surj} xs ys with Surjective? b d o
_⊹_ {b} {d} {o} ∙        ys       | yes surj = ys
_⊹_ {b} {d} {o} xs       ∙        | yes surj = xs
_⊹_ {b} {d} {o} (x ∷ xs) (y ∷ ys) | yes surj with _divMod_ (o + Fin.toℕ x + Fin.toℕ y) b {fromWitnessFalse (>⇒≢ (Surjective⇒base≥1 surj))}
_⊹_ {b} {d} {o} (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq =
    inject≤ remainder b≤d ∷ n+ quotient (_⊹_ {surj = fromWitness surj} xs ys)
    where   b≤d : b ≤ d
            b≤d = Surjective⇒b≤d surj
_⊹_ {b} {d} {o} {()} xs ys | no ¬surj
