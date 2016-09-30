module Data.Num.Suprenum where

open import Data.Num.Core
open import Data.Num.Bounded

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

------------------------------------------------------------------------
--

Suprenum?-lemma-1 : ∀ {b d o}
    → (xs : Num b d o)
    → (sup : Num b d o)
    → Suprenum sup
    → toℕ sup ≢ toℕ xs
    → Suprenum xs
    → ⊥
Suprenum?-lemma-1 xs sup claim p xs-be-suprenum
    = contradiction ⟦xs⟧≥⟦sup⟧ ⟦xs⟧≱⟦sup⟧
    where   ⟦xs⟧≥⟦sup⟧ : toℕ xs ≥ toℕ sup
            ⟦xs⟧≥⟦sup⟧ = xs-be-suprenum sup
            ⟦xs⟧≱⟦sup⟧ : toℕ xs ≱ toℕ sup
            ⟦xs⟧≱⟦sup⟧ = <⇒≱ $ ≤∧≢⇒< (claim xs) (λ x → p (sym x))

Suprenum? : ∀ {b d o}
    → (xs : Num b d o)
    → Dec (Suprenum xs)
Suprenum? {b} {d} {o} xs with boundedView b d o
Suprenum? xs | IsBounded cond with BoundedCond⇒Bounded cond
Suprenum? xs | IsBounded cond | sup , claim with toℕ sup ≟ toℕ xs
Suprenum? xs | IsBounded cond | sup , claim | yes p rewrite p = yes claim
Suprenum? xs | IsBounded cond | sup , claim | no ¬p = no (Suprenum?-lemma-1 xs sup claim ¬p)
Suprenum? xs | IsntBounded cond = no (¬Bounded⇒¬Suprenum (NonBoundedCond⇒¬Bounded cond) xs)
--

next-lemma-2 : ∀ {b}
    → (xs : Num (suc b) 1 0)
    → ¬ (Suprenum xs)
    → Num (suc b) 1 0
next-lemma-2 {b} xs ¬sup = contradiction sup ¬sup
    where   sup : Suprenum xs
            sup ys = HasOnly:0-lemma (suc b) xs ys

next-lemma-1 : ∀ {d o}
    → (x : Digit (suc d))
    → (xs : Num 0 (suc d) o)
    → (¬Suprenum : ¬ (Suprenum (x ∷ xs)))
    → (greatest : Greatest x)
    → Num 0 (suc d) o
next-lemma-1 {d} {o} x xs ¬sup greatest = contradiction sup ¬sup
    where   sup : Suprenum (x ∷ xs)
            sup ys = Base≡0-lemma x xs greatest ys

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


next-lemma-3 : ∀ {b d o}
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → (¬Suprenum : ¬ (Suprenum (x ∷ xs)))
    → (greatest : Greatest x)
    → suc d + o ≥ 2
    → Suprenum xs
    → ⊥
next-lemma-3 {b} {d} {o} x xs ¬sup greatest d+o≥2 claim = contradiction p ¬p
    where   p : toℕ xs ≥ toℕ (x ∷ xs)
            p = claim (x ∷ xs)
            ¬p : toℕ xs ≱ toℕ (x ∷ xs)
            ¬p = <⇒≱ $
                start
                    suc (toℕ xs)
                ≤⟨ reflexive (cong suc (sym (*-right-identity (toℕ xs)))) ⟩
                    suc (toℕ xs * suc zero)
                ≤⟨ s≤s (n*-mono (toℕ xs) (s≤s z≤n)) ⟩
                    suc (toℕ xs * suc b)
                ≤⟨ +n-mono (toℕ xs * suc b) (≤-pred d+o≥2) ⟩
                    d + o + toℕ xs * suc b
                ≤⟨ reflexive (cong (λ w → w + toℕ xs * suc b) (sym (toℕ-greatest x greatest))) ⟩
                    Digit-toℕ x o + toℕ xs * suc b
                □


next : ∀ {b d o}
    → (xs : Num b d o)
    → ¬ (Suprenum xs)
    → Num b d o
next {b} {d} {o} xs ¬sup with boundedView b d o

next ∙         ¬sup | IsBounded (Base≡0 d o)     = z ∷ ∙
next ∙         ¬sup | IsBounded (HasNoDigit b o) = contradiction (HasNoDigit-lemma b o) ¬sup
next ∙         ¬sup | IsBounded (HasOnly:0 b)    = next-lemma-2 ∙ ¬sup
next ∙         ¬sup | IsntBounded (Digit+Offset≥2 b d o d+o≥2)
    = z ∷ ∙
next (x  ∷ xs) ¬sup | cond with Greatest? x
next (x  ∷ xs) ¬sup | IsBounded (Base≡0 d o)     | yes greatest = next-lemma-1 {d} {o} x xs ¬sup greatest
next (() ∷ xs) ¬sup | IsBounded (HasNoDigit b o) | yes greatest
next (x  ∷ xs) ¬sup | IsBounded (HasOnly:0 b)    | yes greatest = next-lemma-2 (x ∷ xs) ¬sup
next (x  ∷ xs) ¬sup | IsntBounded (Digit+Offset≥2 b d o d+o≥2) | yes greatest
    = z ∷ next xs (next-lemma-3 x xs ¬sup greatest d+o≥2)
next (x  ∷ xs) ¬sup | cond | no ¬greatest = digit+1 x ¬greatest ∷ xs

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
