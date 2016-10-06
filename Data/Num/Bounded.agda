module Data.Num.Bounded where

open import Data.Num.Core

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
-- Views

data BoundedCond : ℕ → ℕ → ℕ → Set where
    Base≡0   : ∀ d o → BoundedCond 0       (suc d) o
    HasOnly0 : ∀ b   → BoundedCond (suc b) 1 0

data NonBoundedCond : ℕ → ℕ → ℕ → Set where
    Digit+Offset≥2 : ∀ b d o → (d+o≥2 : suc d + o ≥ 2) → NonBoundedCond (suc b) (suc d) o
    HasNoDigit     : ∀ b   o                           → NonBoundedCond b       0 o

data BoundedView : ℕ → ℕ → ℕ → Set where
    IsBounded   : ∀ {b d o} → (cond :    BoundedCond b d o) → BoundedView b d o
    IsntBounded : ∀ {b d o} → (cond : NonBoundedCond b d o) → BoundedView b d o

boundedView : ∀ b d o → BoundedView b d o
boundedView b       zero          o       = IsntBounded (HasNoDigit b o)
boundedView zero    (suc d)       o       = IsBounded (Base≡0 d o)
boundedView (suc b) (suc zero)    zero    = IsBounded (HasOnly0 b)
boundedView (suc b) (suc zero)    (suc o) = IsntBounded (Digit+Offset≥2 b zero (suc o) (s≤s (s≤s z≤n)))
boundedView (suc b) (suc (suc d)) o       = IsntBounded (Digit+Offset≥2 b (suc d) o (s≤s (s≤s z≤n)))
------------------------------------------------------------------------
-- Relations between Conditions and Predicates

toℕ-Base≡0 : ∀ {d o}
    → (x : Digit d)
    → (xs : Num 0 d o)
    → ⟦ x ∷ xs ⟧ ≡ Digit-toℕ x o
toℕ-Base≡0 {d} {o} x ∙         = +-right-identity (Digit-toℕ x o)
toℕ-Base≡0 {d} {o} x (x' ∷ xs) =
    begin
        Digit-toℕ x o + ⟦ x' ∷ xs ⟧ * 0
    ≡⟨ cong (λ w → Digit-toℕ x o + w) (*-right-zero ⟦ x' ∷ xs ⟧) ⟩
        Digit-toℕ x o + 0
    ≡⟨ +-right-identity (Digit-toℕ x o) ⟩
        Digit-toℕ x o
    ∎

Base≡0-lemma : ∀ {d} {o}
    → (x : Digit (suc d))
    → (xs : Num 0 (suc d) o)
    → Greatest x
    → Maximum x xs
Base≡0-lemma {_} {o} x xs greatest y ys        =
    start
        ⟦ y ∷ ys ⟧
    ≈⟨ toℕ-Base≡0 y ys ⟩
        Digit-toℕ y o
    ≤⟨ greatest-of-all o x y greatest ⟩
        Fin.toℕ x + o
    ≈⟨ sym (toℕ-Base≡0 x xs) ⟩
        ⟦ x ∷ xs ⟧
    □

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

HasOnly0-all-zero : ∀ {b} → (x : Digit 1) (xs : Num b 1 0) → ⟦ x ∷ xs ⟧ ≡ 0
HasOnly0-all-zero     z      ∙         = refl
HasOnly0-all-zero {b} z      (x' ∷ xs) = cong (λ x' → x' * b) (HasOnly0-all-zero {b} x' xs)
HasOnly0-all-zero     (s ()) xs

HasOnly0-Maximum : ∀ b → (x : Digit 1) (xs : Num b 1 0) → Maximum x xs
HasOnly0-Maximum b x xs y ys = reflexive $
    begin
        ⟦ y ∷ ys ⟧
    ≡⟨ HasOnly0-all-zero y ys ⟩
        0
    ≡⟨ sym (HasOnly0-all-zero x xs) ⟩
        ⟦ x ∷ xs ⟧
    ∎

Digit+Offset≥2-¬Bounded-lemma : ∀ b d o → d + o ≥ 1 → ¬ (Bounded (suc b) (suc d) o)
Digit+Offset≥2-¬Bounded-lemma b d o d+o≥1 (x , xs , claim) = contradiction p ¬p
    where
        p : ⟦ x ∷ xs ⟧ ≥ ⟦ greatest-digit d ∷ (x ∷ xs) ⟧
        p = claim (greatest-digit d) (x ∷ xs)
        ¬p : ⟦ x ∷ xs ⟧ ≱ ⟦ greatest-digit d ∷ (x ∷ xs) ⟧
        ¬p = <⇒≱ $
            start
                suc ⟦ x ∷ xs ⟧
            ≈⟨ cong suc (sym (*-right-identity ⟦ x ∷ xs ⟧)) ⟩
                suc (⟦ x ∷ xs ⟧ * 1)
            ≤⟨ s≤s (n*-mono ⟦ x ∷ xs ⟧ (s≤s z≤n)) ⟩
                suc (⟦ x ∷ xs ⟧ * suc b)
            ≤⟨ +n-mono (⟦ x ∷ xs ⟧ * suc b) d+o≥1 ⟩
                (d + o) + (⟦ x ∷ xs ⟧ * suc b)
            ≈⟨ cong
                (λ w → w + ⟦ x ∷ xs ⟧ * suc b)
                (sym (toℕ-greatest (Fin.fromℕ d) (greatest-digit-is-the-Greatest d)))
            ⟩
                Digit-toℕ (greatest-digit d) o + ⟦ x ∷ xs ⟧ * suc b
            □

HasNoDigit-¬Bounded-lemma : ∀ b o → ¬ (Bounded b 0 o)
HasNoDigit-¬Bounded-lemma b o (() , xs , claim)

BoundedCond⇒Bounded : ∀ {b d o} → BoundedCond b d o → Bounded b d o
BoundedCond⇒Bounded (Base≡0 d o) = greatest-digit d , ∙ , Base≡0-lemma (greatest-digit d) ∙ (greatest-digit-is-the-Greatest d)
BoundedCond⇒Bounded (HasOnly0 b) = z , ∙ , (HasOnly0-Maximum (suc b) z ∙)

NonBoundedCond⇒¬Bounded : ∀ {b d o} → NonBoundedCond b d o → ¬ (Bounded b d o)
NonBoundedCond⇒¬Bounded (Digit+Offset≥2 b d o d+o≥2) = Digit+Offset≥2-¬Bounded-lemma b d o (≤-pred d+o≥2)
NonBoundedCond⇒¬Bounded (HasNoDigit b o)             = HasNoDigit-¬Bounded-lemma b o

Bounded⇒BoundedCond : ∀ {b d o} → Bounded b d o → BoundedCond b d o
Bounded⇒BoundedCond {b} {d} {o} bounded with boundedView b d o
Bounded⇒BoundedCond bounded | IsBounded condition = condition
Bounded⇒BoundedCond bounded | IsntBounded condition = contradiction bounded (NonBoundedCond⇒¬Bounded condition)

¬Bounded⇒NonBoundedCond : ∀ {b d o} → ¬ (Bounded b  d o) → NonBoundedCond b d o
¬Bounded⇒NonBoundedCond {b} {d} {o} ¬bounded with boundedView b d o
¬Bounded⇒NonBoundedCond ¬bounded | IsBounded condition = contradiction (BoundedCond⇒Bounded condition) ¬bounded
¬Bounded⇒NonBoundedCond ¬bounded | IsntBounded condition = condition

Bounded? : ∀ {b d o} → BoundedView b d o → Dec (Bounded b d o)
Bounded? (IsBounded condition)   = yes (BoundedCond⇒Bounded condition)
Bounded? (IsntBounded condition) = no (NonBoundedCond⇒¬Bounded condition)


--------------------------------------------------------------------------------
-- Misc

¬Bounded⇒¬Maximum : ∀ {b d o}
    → ¬ (Bounded b d o)
    → (x : Digit d)
    → (xs : Num b d o)
    → Maximum x xs
    → ⊥
¬Bounded⇒¬Maximum ¬bounded x xs claim =
    contradiction (x , xs , claim) ¬bounded

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
