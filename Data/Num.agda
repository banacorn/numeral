module Data.Num where

open import Data.Num.Core public
open import Data.Num.Surjection public

open import Data.Nat
open import Data.Nat.Properties.Extra
open import Data.Nat.DM
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)

open import Relation.Nullary
open import Relation.Nullary.Decidable


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


-- _⊹_ : ∀ {b d o}
--     → {isSurj : IsSurjective b d o}
--     → (xs ys : Num b d o)
--     → Num b d o
-- _⊹_ {b} {d} {o}      xs       ys        with surjectionView b d o
-- _⊹_ {b} {d} {o}      ∙        ∙        | Surj cond = ∙
-- _⊹_ {b} {d} {o}      ∙        (y ∷ ys) | Surj cond = y ∷ ys
-- _⊹_ {b} {d} {o}      (x ∷ xs) ∙        | Surj cond = x ∷ xs
-- _⊹_ {b} {d} {o}      (x ∷ xs) (y ∷ ys) | Surj cond with _divMod_ (o + Fin.toℕ x + Fin.toℕ y) b {fromWitnessFalse (>⇒≢ (SurjCond⇒b≥1 cond))}
-- _⊹_ {b} {d} {o}      (x ∷ xs) (y ∷ ys) | Surj cond | result quotient remainder property div-eq mod-eq =
--     inject≤ remainder d≥b ∷ n+ quotient (_⊹_ {isSurj = SurjCond⇒IsSurj cond} xs ys)
--     where   d≥b : d ≥ b
--             d≥b = SurjCond⇒d≥b cond
-- _⊹_ {b} {d} {o} {()} xs ys | NonSurj _
