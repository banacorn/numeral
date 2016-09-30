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
-- a system is bounded if there exists the greatest number

Bounded : ∀ b d o → Set
Bounded b d o = Σ[ xs ∈ Num b d o ] ∀ (ys : Num b d o) → toℕ xs ≥ toℕ ys

------------------------------------------------------------------------
-- Views

data BoundedCond : ℕ → ℕ → ℕ → Set where
    Base≡0     : ∀ d o → BoundedCond 0       (suc d) o
    HasNoDigit : ∀ b o → BoundedCond b       0       o
    HasOnly:0  : ∀ b   → BoundedCond (suc b) 1       0

data NonBoundedCond : ℕ → ℕ → ℕ → Set where
    Digit+Offset≥2 : ∀ b d o → (d+o≥2 : suc d + o ≥ 2) → NonBoundedCond (suc b) (suc d) o

data BoundedView : ℕ → ℕ → ℕ → Set where
    IsBounded  : ∀ {b d o} → BoundedCond b d o → BoundedView b d o
    IsntBounded : ∀ {b d o} → NonBoundedCond b d o → BoundedView b d o

boundedView : ∀ b d o → BoundedView b d o
boundedView b       0             o = IsBounded (HasNoDigit b o)
boundedView 0       (suc d)       o = IsBounded (Base≡0 d o)
boundedView (suc b) 1             0 = IsBounded (HasOnly:0 b)
boundedView (suc b) 1             (suc o)
    = IsntBounded (Digit+Offset≥2 b zero (suc o) (s≤s (s≤s z≤n)))
boundedView (suc b) (suc (suc d)) o
    = IsntBounded (Digit+Offset≥2 b (suc d) o (s≤s (s≤s z≤n)))

------------------------------------------------------------------------
-- Relations between Conditions and Predicates

Base≡0-lemma : ∀ d o → (xs : Num 0 (suc d) o) → toℕ {0} {suc d} {o} (greatest-digit d ∷ ∙) ≥ toℕ xs
Base≡0-lemma d o ∙ = z≤n
Base≡0-lemma d o (x ∷ xs) =
    start
        -- toℕ (x ∷ xs)
        Fin.toℕ x + o + toℕ xs * zero
    ≤⟨ reflexive (cong (λ w → Digit-toℕ x o + w) (*-right-zero (toℕ xs))) ⟩
        Fin.toℕ x + o + zero
    ≤⟨ +n-mono 0 (+n-mono o $ ≤-pred (bounded x)) ⟩
        d + o + zero
    ≤⟨ reflexive (cong (λ w → w + 0) (sym (greatest-digit-toℕ d o))) ⟩
        -- toℕ (greatest-digit d ∷ ∙)
        Fin.toℕ (Fin.fromℕ d) + o + zero
    □

HasNoDigit-lemma : ∀ b o → (xs : Num b 0 o) → 0 ≥ toℕ xs
HasNoDigit-lemma b o ∙         = z≤n
HasNoDigit-lemma b o (() ∷ xs)

HasOnly:0-lemma : ∀ b → (xs : Num b 1 0) → 0 ≥ toℕ xs
HasOnly:0-lemma b ∙ = z≤n
HasOnly:0-lemma b (z ∷ xs) = *n-mono b (HasOnly:0-lemma b xs)
HasOnly:0-lemma b (s () ∷ xs)

Digit+Offset≥2-lemma : ∀ b d o → d + o ≥ 1 → ¬ (Bounded (suc b) (suc d) o)
Digit+Offset≥2-lemma b d o d+o≥1 (evidence , claim) = contradiction p ¬p
    where
        p : toℕ evidence ≥ toℕ (greatest-digit d ∷ evidence)
        p = claim (greatest-digit d ∷ evidence)
        ¬p : toℕ evidence ≱ toℕ (greatest-digit d ∷ evidence)
        ¬p = <⇒≱ $
            start
                suc (toℕ evidence)
            ≤⟨ reflexive (cong suc (sym (*-right-identity (toℕ evidence)))) ⟩
                suc (toℕ evidence * 1)
            ≤⟨ s≤s (n*-mono (toℕ evidence) (s≤s z≤n)) ⟩
                suc (toℕ evidence * suc b)
            ≤⟨ +n-mono (toℕ evidence * suc b) d+o≥1 ⟩
                (d + o) + (toℕ evidence * suc b)
            ≤⟨ reflexive
                (cong
                    (λ w → w + toℕ evidence * suc b)
                    (sym (greatest-digit-toℕ d o))
                )
            ⟩
                Digit-toℕ (greatest-digit d) o + toℕ evidence * suc b
            □

BoundedCond⇒Bounded : ∀ {b d o} → BoundedCond b d o → Bounded b d o
BoundedCond⇒Bounded (Base≡0 d o)     = (greatest-digit d ∷ ∙) , (Base≡0-lemma d o)
BoundedCond⇒Bounded (HasNoDigit b o) = ∙ , (HasNoDigit-lemma b o)
BoundedCond⇒Bounded (HasOnly:0 b)    = ∙ , (HasOnly:0-lemma (suc b))

NonBoundedCond⇒¬Bounded : ∀ {b d o} → NonBoundedCond b d o → ¬ (Bounded b d o)
NonBoundedCond⇒¬Bounded (Digit+Offset≥2 b d o d+o≥2)
    = Digit+Offset≥2-lemma b d o (≤-pred d+o≥2)

Bounded⇒BoundedCond : ∀ {b d o} → Bounded b d o → BoundedCond b d o
Bounded⇒BoundedCond {b} {d} {o} bounded with boundedView b d o
Bounded⇒BoundedCond bounded | IsBounded condition = condition
Bounded⇒BoundedCond bounded | IsntBounded condition = contradiction bounded (NonBoundedCond⇒¬Bounded condition)

¬Bounded⇒NonBoundedCond : ∀ {b d o} → ¬ (Bounded b d o) → NonBoundedCond b d o
¬Bounded⇒NonBoundedCond {b} {d} {o} ¬bounded with boundedView b d o
¬Bounded⇒NonBoundedCond ¬bounded | IsBounded condition = contradiction (BoundedCond⇒Bounded condition) ¬bounded
¬Bounded⇒NonBoundedCond ¬bounded | IsntBounded condition = condition

Bounded? : ∀ {b d o} → BoundedView b d o → Dec (Bounded b d o)
Bounded? (IsBounded condition) = yes (BoundedCond⇒Bounded condition)
Bounded? (IsntBounded condition) = no (NonBoundedCond⇒¬Bounded condition)

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
