module Data.Num.Continuous where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
open import Data.Num.Incrementable

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

Continuous : ∀ b d o → Set
Continuous b d o = (xs : Num b d o) → Incrementable xs

data ContinuousCond : ℕ → ℕ → ℕ → Set where
    continuousCond : ∀ {b} {d} {o}
        → NonBoundedCond b d o
        → (abundant : Abundant b d o)
        → ContinuousCond b d o


Continuous-Others-¬Maximum : ∀ {b d o}
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (xs : Num (suc b) (suc d) o)
    → ¬ (Maximum xs)
Continuous-Others-¬Maximum {b} {d} {o} d+o≥2 xs = ¬Bounded⇒¬Maximum xs (NonBoundedCond⇒¬Bounded (Others b d o d+o≥2))

Continuous-Others-Incremental : ∀ {b d o}
    → (abundant : Abundant (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (xs : Num (suc b) (suc d) o)
    → let
        ¬max = Continuous-Others-¬Maximum d+o≥2 xs
        next = next-number-Others xs ¬max d+o≥2
      in ⟦ next ⟧ ≡ 1 + ⟦ xs ⟧
Continuous-Others-Incremental {b} {d} {o} abundant d+o≥2 (x ∙) with Others-view-single b d o x
Continuous-Others-Incremental {b} {d} {o} abundant d+o≥2 (x ∙) | NeedNoCarry ¬greatest = Digit-toℕ-digit+1 x ¬greatest
Continuous-Others-Incremental {b} {d} {o} abundant d+o≥2 (x ∙) | Gapped greatest gapped =
    let
        eq : (1 ⊔ o) * suc b ≡ suc d
        eq = IsPartialOrder.antisym isPartialOrder abundant gapped
    in
    begin
        o + Digit-toℕ (1⊔o d o d+o≥2) o * suc b
    ≡⟨ cong (λ w → o + w * suc b) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
        o + (suc zero ⊔ o) * suc b
    ≡⟨ cong (λ w → o + w) eq ⟩
        o + suc d
    ≡⟨ cong (λ w → o + w) (sym greatest) ⟩
        o + suc (Fin.toℕ x)
    ≡⟨ +-comm o (suc (Fin.toℕ x)) ⟩
        suc (Fin.toℕ x + o)
    ∎
Continuous-Others-Incremental {b} {d} {o} abundant d+o≥2 (x ∙) | ¬Gapped greatest ¬gapped =
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
        Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + Digit-toℕ (1⊔o d o d+o≥2) o * suc b
    ≡⟨ cong₂ (λ v w → v + w * suc b) (Digit-toℕ-digit+1-n x greatest ((suc zero ⊔ o) * suc b) lower-bound abundant) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
        ((suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b) + (suc zero ⊔ o) * suc b)
    ≡⟨ m∸n+n≡m {suc (Fin.toℕ x + o)} {(suc zero ⊔ o) * suc b} prop ⟩
        suc (Fin.toℕ x + o)
    ∎
Continuous-Others-Incremental {b} {d} {o} abundant d+o≥2 (x ∷ xs) with Others-view x xs (Continuous-Others-¬Maximum d+o≥2 (x ∷ xs)) d+o≥2
Continuous-Others-Incremental {b} {d} {o} abundant d+o≥2 (x ∷ xs) | NeedNoCarry ¬greatest =
        begin
            (Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * suc b)
        ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) (Digit-toℕ-digit+1 x ¬greatest) ⟩
            suc (Digit-toℕ x o + ⟦ xs ⟧ * suc b)
        ∎
Continuous-Others-Incremental {b} {d} {o} abundant d+o≥2 (x ∷ xs) | Gapped greatest gapped =
        let
            ¬max = next-number-¬Maximum xs d+o≥2
            next = next-number-Others xs ¬max d+o≥2
            next>xs = ≤-pred $ ≤-step $ next-number-is-greater-Others xs ¬max d+o≥2
            ⟦next⟧∸⟦xs⟧≡1 : ⟦ next ⟧ ∸ ⟦ xs ⟧ ≡ 1
            ⟦next⟧∸⟦xs⟧≡1 = cancel-+-right ⟦ xs ⟧ {⟦ next ⟧ ∸ ⟦ xs ⟧} {1} $
                begin
                    ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
                ≡⟨ m∸n+n≡m next>xs ⟩
                    ⟦ next ⟧
                ≡⟨ Continuous-Others-Incremental abundant d+o≥2 xs ⟩
                    1 + ⟦ xs ⟧
                ∎

            ¬redundant : suc b ≥ suc d
            ¬redundant =
                start
                    suc d
                ≤⟨ gapped ⟩
                    (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b
                ≈⟨ cong (λ w → w * suc b) ⟦next⟧∸⟦xs⟧≡1 ⟩
                    suc (b + zero)
                ≈⟨ +-right-identity (suc b) ⟩
                    suc b
                □
            abundant' : suc b ≤ suc d
            abundant' =
                start
                    suc b
                ≈⟨ sym (+-right-identity (suc b)) ⟩
                    suc (b + zero)
                ≤⟨ *n-mono (suc b) (m≤m⊔n 1 o) ⟩
                    (suc zero ⊔ o) * suc b
                ≤⟨ abundant ⟩
                    suc d
                □
            b≡d : suc b ≡ suc d
            b≡d = IsPartialOrder.antisym isPartialOrder abundant' ¬redundant

        in -- z ∷ next
        begin
            o + ⟦ next ⟧ * suc b
        ≡⟨ cong (λ w → (o + w * suc b)) (Continuous-Others-Incremental abundant d+o≥2 xs) ⟩
            o + (suc b + ⟦ xs ⟧ * suc b)
        ≡⟨ sym (+-assoc o (suc b) (⟦ xs ⟧ * suc b)) ⟩
            o + suc b + ⟦ xs ⟧ * suc b
        ≡⟨ cong (λ w → o + w + ⟦ xs ⟧ * suc b) b≡d ⟩
            o + suc d + ⟦ xs ⟧ * suc b
        ≡⟨ cong (λ w → o + w + ⟦ xs ⟧ * suc b) (sym greatest) ⟩
            o + suc (Fin.toℕ x) + ⟦ xs ⟧ * suc b
        ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) (+-comm o (suc (Fin.toℕ x))) ⟩
            suc (Fin.toℕ x + o + ⟦ xs ⟧ * suc b)
        ∎
Continuous-Others-Incremental {b} {d} {o} abundant d+o≥2 (x ∷ xs) | ¬Gapped greatest ¬gapped =
    let
        ¬max = next-number-¬Maximum xs d+o≥2
        next = next-number-Others xs ¬max d+o≥2
        gap = (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b
        gap>0 = (start
                1
            ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ xs ⟧))) ⟩
                suc (⟦ xs ⟧ ∸ ⟦ xs ⟧)
            ≈⟨ sym (+-∸-assoc 1 {⟦ xs ⟧} ≤-refl) ⟩
                suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
            ≤⟨ ∸-mono {suc ⟦ xs ⟧} {⟦ next ⟧} {⟦ xs ⟧} (next-number-is-greater-Others xs ¬max d+o≥2) ≤-refl ⟩
                ⟦ next ⟧ ∸ ⟦ xs ⟧
            □) *-mono (s≤s {0} {b} z≤n)
        next>xs = <⇒≤ $ next-number-is-greater-Others xs ¬max d+o≥2
    in -- digit+1-n x greatest gap gap>0 ∷ next
    begin
        (Digit-toℕ (digit+1-n x greatest gap gap>0) o + ⟦ next ⟧ * suc b)
    ≡⟨ cong (λ w → w + ⟦ next ⟧ * suc b) (Digit-toℕ-digit+1-n x greatest gap gap>0 (<⇒≤ ¬gapped)) ⟩
        suc (Digit-toℕ x o) ∸ gap + ⟦ next ⟧ * suc b
    ≡⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + ⟦ next ⟧ * suc b) (*-distrib-∸ʳ (suc b) ⟦ next ⟧ ⟦ xs ⟧) ⟩
        suc (Digit-toℕ x o) ∸ (⟦ next ⟧ * suc b ∸ ⟦ xs ⟧ * suc b) + ⟦ next ⟧ * suc b
    ≡⟨ m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ xs ⟧ * suc b) (⟦ next ⟧ * suc b) (*n-mono (suc b) next>xs) $
        start
            ⟦ next ⟧ * suc b ∸ ⟦ xs ⟧ * suc b
        ≈⟨ sym (*-distrib-∸ʳ (suc b) ⟦ next ⟧ ⟦ xs ⟧) ⟩
            gap
        ≤⟨ ≤-pred ¬gapped ⟩
            d
        ≤⟨ ≤-step (m≤m+n d o) ⟩
            suc (d + o)
        ≈⟨ cong (λ w → w + o) (sym greatest) ⟩
            suc (Fin.toℕ x + o)
        □ ⟩
        suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
    ∎

ContinuousCond⇒Continuous : ∀ {b d o}
    → ContinuousCond b d o
    → Continuous b d o
ContinuousCond⇒Continuous (continuousCond (Others b d o d+o≥2) prop) xs
    = (next-number-Others xs (Continuous-Others-¬Maximum d+o≥2 xs) d+o≥2) , Continuous-Others-Incremental prop d+o≥2 xs
ContinuousCond⇒Continuous (continuousCond (NoDigits b d) prop) xs
    = NoDigits-explode xs

Bounded⇒¬Continuous : ∀ {b d o}
    → Bounded b d o
    → ¬ (Continuous b d o)
Bounded⇒¬Continuous (xs , max) claim = contradiction (claim xs) (Maximum⇒¬Incrementable xs max)

Others∧¬Abundant⇒¬Continuous : ∀ {b d o}
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ¬ (Abundant (suc b) (suc d) o)
    → ¬ (Continuous (suc b) (suc d) o)
Others∧¬Abundant⇒¬Continuous {b} {d} {o} d+o≥2 ¬abundant claim = {!   !}

Continuous? : ∀ b d o → Dec (Continuous b d o)
Continuous? b d o with boundedView b d o
Continuous? b d o | IsBounded cond = no (Bounded⇒¬Continuous (BoundedCond⇒Bounded cond))
Continuous? _ _ _ | IsntBounded (Others b d o d+o≥2) with Abundant? (suc b) (suc d) o
Continuous? _ _ _ | IsntBounded (Others b d o d+o≥2) | yes abundant
    = yes (λ xs → (next-number-Others xs (Continuous-Others-¬Maximum d+o≥2 xs) d+o≥2) , (Continuous-Others-Incremental abundant d+o≥2 xs))
Continuous? _ _ _ | IsntBounded (Others b d o d+o≥2) | no ¬abundant
    = no (Others∧¬Abundant⇒¬Continuous d+o≥2 ¬abundant)
Continuous? _ _ _ | IsntBounded (NoDigits b o) = yes (λ xs → NoDigits-explode xs)

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
