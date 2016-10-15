module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next

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

Continuous-Others-¬Maximum : ∀ {b d o}
    → (abundant : suc d ≥ (1 ⊔ o) * suc b)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (xs : Num (suc b) (suc d) o)
    → ¬ (Maximum xs)
Continuous-Others-¬Maximum {b} {d} {o} abundant d+o≥2 xs with boundedView (suc b) (suc d) o
Continuous-Others-¬Maximum abundant (s≤s ()) xs | IsBounded (AllZeros b)
Continuous-Others-¬Maximum abundant d+o≥2    xs | IsntBounded cond = ¬Bounded⇒¬Maximum xs (NonBoundedCond⇒¬Bounded cond)

Continuous-Others-lemma : ∀ {b d o}
    → (abundant : suc d ≥ (1 ⊔ o) * suc b)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (xs : Num (suc b) (suc d) o)
    → let
        ¬max = Continuous-Others-¬Maximum abundant d+o≥2 xs
        next  = next-number xs ¬max
      in ⟦ next ⟧ ∸ ⟦ xs ⟧ ≡ 1
Continuous-Others-lemma {b} {d} {o} abundant d+o≥2 xs with boundedView (suc b) (suc d) o
Continuous-Others-lemma abundant (s≤s ()) xs | IsBounded (AllZeros b)
Continuous-Others-lemma abundant _ (x ∙) | IsntBounded (Others b d o d+o≥2) with Others-view-single b d o x
Continuous-Others-lemma abundant _ (x ∙) | IsntBounded (Others b d o d+o≥2) | NeedNoCarry ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o ∸ (Fin.toℕ x + o)
    ≡⟨ cong (λ w → w ∸ (Fin.toℕ x + o)) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Digit-toℕ x o) ∸ (Fin.toℕ x + o)
    ≡⟨ refl ⟩
        suc (Fin.toℕ x + o) ∸ (Fin.toℕ x + o)
    ≡⟨ +-∸-assoc 1 {Fin.toℕ x + o} {Fin.toℕ x + o} ≤-refl ⟩
        suc ((Fin.toℕ x + o) ∸ (Fin.toℕ x + o))
    ≡⟨ cong suc (n∸n≡0 (Fin.toℕ x + o)) ⟩
        suc zero
    ∎
Continuous-Others-lemma abundant _ (x ∙) | IsntBounded (Others b d o d+o≥2) | Gapped greatest gapped =
    let
        eq : (1 ⊔ o) * suc b ≡ suc d
        eq = IsPartialOrder.antisym isPartialOrder abundant gapped
    in
    begin
        o + Digit-toℕ (1⊔o d o d+o≥2) o * suc b ∸ Digit-toℕ x o
    ≡⟨ cong (λ w → o + w * suc b ∸ Digit-toℕ x o) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
        o + (suc zero ⊔ o) * suc b ∸ Digit-toℕ x o
    ≡⟨ cong (λ w → o + w ∸ Digit-toℕ x o) eq ⟩
        o + suc d ∸ (Fin.toℕ x + o)
    ≡⟨ cong (λ w → o + w ∸ Digit-toℕ x o) (sym greatest) ⟩
        o + suc (Fin.toℕ x) ∸ (Fin.toℕ x + o)
    ≡⟨ cong (λ w → w ∸ (Fin.toℕ x + o)) (+-comm o (suc (Fin.toℕ x))) ⟩
        suc (Fin.toℕ x + o) ∸ (Fin.toℕ x + o)
    ≡⟨ +-∸-assoc 1 {Fin.toℕ x + o} {Fin.toℕ x + o} ≤-refl ⟩
        suc ((Fin.toℕ x + o) ∸ (Fin.toℕ x + o))
    ≡⟨ cong suc (n∸n≡0 (Fin.toℕ x + o)) ⟩
        suc zero
    ∎
Continuous-Others-lemma abundant _ (x ∙) | IsntBounded (Others b d o d+o≥2) | ¬Gapped greatest ¬gapped =
    let
        lower-bound : (1 ⊔ o) * suc b > 0
        lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n
        prop : (suc zero ⊔ o) * suc b ≤ suc (Fin.toℕ x + o)
        prop = start
                (suc zero ⊔ o) * suc b
            ≤⟨ ≤-pred ¬gapped ⟩
                d
            ≈⟨ suc-injective (sym greatest) ⟩
                Fin.toℕ x
            ≤⟨ ≤-step (m≤m+n (Fin.toℕ x) o) ⟩
                suc (Fin.toℕ x + o)
            □

    in
    begin
        Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + Digit-toℕ (1⊔o d o d+o≥2) o * suc b ∸ Digit-toℕ x o
    ≡⟨ cong₂ (λ v w → v + w * suc b ∸ Digit-toℕ x o) (Digit-toℕ-digit+1-n x greatest ((suc zero ⊔ o) * suc b) lower-bound abundant) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
        ((suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b) + (suc zero ⊔ o) * suc b) ∸ (Fin.toℕ x + o)
    ≡⟨ cong (λ w → w ∸ (Fin.toℕ x + o)) (m∸n+n≡m {suc (Fin.toℕ x + o)} {(suc zero ⊔ o) * suc b} prop) ⟩
        suc (Fin.toℕ x + o) ∸ (Fin.toℕ x + o)
    ≡⟨ +-∸-assoc 1 {Fin.toℕ x + o} {Fin.toℕ x + o} ≤-refl ⟩
        suc ((Fin.toℕ x + o) ∸ (Fin.toℕ x + o))
    ≡⟨ cong suc (n∸n≡0 (Fin.toℕ x + o)) ⟩
        suc zero
    ∎
Continuous-Others-lemma abundant _ (x ∷ xs) | IsntBounded (Others b d o d+o≥2) with Others-view x xs (Continuous-Others-¬Maximum abundant d+o≥2 (x ∷ xs)) d+o≥2
Continuous-Others-lemma abundant _ (x ∷ xs) | IsntBounded (Others b d o d+o≥2) | NeedNoCarry ¬greatest = {!   !}
        -- begin
        --     (Digit-toℕ (digit+1 {! x  !} {! ¬greatest  !}) o + ⟦ xs ⟧ * suc b) ∸ (Digit-toℕ x o + ⟦ xs ⟧ * suc b)
        -- ≡⟨ {!   !} ⟩
        --     {!   !}
        -- ≡⟨ {!   !} ⟩
        --     {!   !}
        -- ≡⟨ {!   !} ⟩
        --     {!   !}
        -- ≡⟨ {!   !} ⟩
        --     suc zero
        -- ∎
        -- = reflexive $ cong (λ w → w + ⟦ xs ⟧ * suc b) (sym (Digit-toℕ-digit+1 x ¬greatest))
Continuous-Others-lemma abundant _ (x ∷ xs) | IsntBounded (Others b d o d+o≥2) | Gapped greatest gapped = {!   !}
Continuous-Others-lemma abundant _ (x ∷ xs) | IsntBounded (Others b d o d+o≥2) | ¬Gapped greatest ¬gapped = {!   !}

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
