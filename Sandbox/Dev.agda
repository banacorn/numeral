module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra

open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)

open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)
open import Data.Product
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import Function
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

next-number-is-LUB : ∀ {b d o}
    → (xs : Num b d o)
    → (ys : Num b d o)
    → (xs! : ¬ (Null xs))
    → (ys! : ¬ (Null ys))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ ys ⟧ ys! > ⟦ xs ⟧ xs!
    → ⟦ ys ⟧ ys! ≥ ⟦ next-number xs xs! ¬max ⟧ next-number-¬Null xs xs! ¬max
next-number-is-LUB {b} {d} {o} xs ys xs! ys! ¬max prop with boundedView b d o
next-number-is-LUB xs ys xs! ys! ¬max prop | IsBounded (Base≡0 d o) = next-number-is-LUB-Base≡0 xs ys xs! ys! ¬max prop
next-number-is-LUB xs ys xs! ys! ¬max prop | IsBounded (HasOnly0 b) = next-number-is-LUB-HasOnly0 xs ys xs! ys! ¬max prop
next-number-is-LUB xs ys xs! ys! ¬max prop | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-is-LUB-d+o≥2 xs ys xs! ys! ¬max d+o≥2 prop
next-number-is-LUB xs ys xs! ys! ¬max prop | IsntBounded (HasNoDigit b o) = next-number-is-LUB-HasNoDigit xs ys xs! ys! ¬max prop
-- start
--     {!   !}
-- ≈⟨ {!   !} ⟩
--     {!   !}
-- ≈⟨ {!   !} ⟩
--     {!   !}
-- ≈⟨ {!   !} ⟩
--     {!   !}
-- □

-- begin
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ∎
-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- □
