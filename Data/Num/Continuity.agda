module Data.Num.Continuity where

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
-- open import Function.Equality using (_⟶_; _⟨$⟩_)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

-- a system is bounded if there exists the greatest number
Bounded : ∀ b d o → Set
Bounded b d o = Σ[ xs ∈ Num b d o ] ∀ (ys : Num b d o) → toℕ xs ≥ toℕ ys

Bounded-lemma-1 : ∀ b o → (xs : Num b 0 o) → 0 ≥ toℕ xs
Bounded-lemma-1 b o ∙         = z≤n
Bounded-lemma-1 b o (() ∷ xs)

Bounded-lemma-2 : ∀ d o → (xs : Num 0 (suc d) o) → toℕ {0} {suc d} {o} (greatest-digit d ∷ ∙) ≥ toℕ xs
Bounded-lemma-2 d o ∙ = z≤n
Bounded-lemma-2 d o (x ∷ xs) =
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

Bounded-lemma-3 : ∀ b → (xs : Num b 1 0) → 0 ≥ toℕ xs
Bounded-lemma-3 b ∙ = z≤n
Bounded-lemma-3 b (z ∷ xs) = *n-mono b (Bounded-lemma-3 b xs)
Bounded-lemma-3 b (s () ∷ xs)


Bounded-lemma-5 : ∀ b d o → ¬ (Bounded (suc b) (suc d) (suc o))
Bounded-lemma-5 b d o (evidence , claim) = contradiction p ¬p
    where
        p : toℕ evidence ≥ toℕ (greatest-digit d ∷ evidence)
        p = claim (greatest-digit d ∷ evidence)
        ¬p : toℕ evidence ≱ toℕ (greatest-digit d ∷ evidence)
        ¬p = <⇒≱ $ start
                suc (toℕ evidence)
            ≤⟨ reflexive (cong suc (sym (*-right-identity (toℕ evidence)))) ⟩
                suc (toℕ evidence * 1)
            ≤⟨ s≤s (n*-mono (toℕ evidence) (s≤s z≤n)) ⟩
                suc (toℕ evidence * suc b)
            ≤⟨ +n-mono (toℕ evidence * suc b) {suc zero} {suc d + o} (s≤s z≤n) ⟩
                (suc d + o) + (toℕ evidence * suc b)
            ≤⟨ reflexive (cong (λ w → w + toℕ evidence * suc b) $
                begin
                    suc (d + o)
                ≡⟨ sym (+-suc d o) ⟩
                    d + suc o
                ≡⟨ sym (greatest-digit-toℕ d (suc o)) ⟩
                    Digit-toℕ (greatest-digit d) (suc o)
                ∎
            ) ⟩
                Digit-toℕ (greatest-digit d) (suc o) + toℕ evidence * suc b
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

Bounded-lemma-6 : ∀ b d o → ¬ (Bounded (suc b) (suc (suc d)) o)
Bounded-lemma-6 b d o (evidence , claim) = contradiction p ¬p
    where
        p : toℕ evidence ≥ toℕ (greatest-digit (suc d) ∷ evidence)
        p = claim (greatest-digit (suc d) ∷ evidence)
        ¬p : toℕ evidence ≱ toℕ (greatest-digit (suc d) ∷ evidence)
        ¬p = <⇒≱ $ s≤s $ start
                toℕ evidence
            ≤⟨ reflexive (sym (*-right-identity (toℕ evidence))) ⟩
                toℕ evidence * suc zero
            ≤⟨ n*-mono (toℕ evidence) (s≤s z≤n) ⟩
                toℕ evidence * suc b
            ≤⟨ n≤m+n (Digit-toℕ (greatest-digit d) o) (toℕ evidence * suc b) ⟩
                Digit-toℕ (greatest-digit d) o + toℕ evidence * suc b
            □


Bounded? : ∀ b d o → Dec (Bounded b d o)
Bounded? zero zero o = yes (∙ , Bounded-lemma-1 zero o)
Bounded? zero (suc d) o = yes ((greatest-digit d ∷ ∙) , Bounded-lemma-2 d o)
Bounded? (suc zero) zero o = yes (∙ , (Bounded-lemma-1 (suc zero) o))
Bounded? (suc zero) (suc zero) zero = yes (∙ , (Bounded-lemma-3 (suc zero)))
Bounded? (suc zero) (suc zero) (suc o) = no (Bounded-lemma-5 zero zero o)
Bounded? (suc zero) (suc (suc d)) o = no (Bounded-lemma-6 zero d o)
Bounded? (suc (suc b)) zero o = yes (∙ , (Bounded-lemma-1 (suc (suc b)) o))
Bounded? (suc (suc b)) (suc zero) zero = yes (∙ , (Bounded-lemma-3 (suc (suc b))))
Bounded? (suc (suc b)) (suc zero) (suc o) = no (Bounded-lemma-5 (suc b) zero o)
Bounded? (suc (suc b)) (suc (suc d)) o = no (Bounded-lemma-6 (suc b) d o)
-- Bounded? (suc b) zero o = yes (∙ , Bounded-lemma-1 (suc b) o)
-- Bounded? (suc b) (suc d) o = {! b  !}

-- Bounded? b zero o = yes (∙ , (Bounded-lemma-1 b o))
-- -- only has the digit "0"
-- Bounded? b (suc zero) zero = yes (∙ , Bounded-lemma-3 b)
-- Bounded? zero (suc zero) (suc o) = {!   !}
-- Bounded? (suc b) (suc zero) (suc o) = {!   !}
-- Bounded? b (suc (suc d)) o = {!   !}

-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
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
