module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
open import Data.Num.Incrementable
-- open import Data.Num.Continuous

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

-- Incrementable : ∀ {b d o} → (xs : Num b d o) → Set
-- Incrementable {b} {d} {o} xs = Σ[ xs' ∈ Num b d o ] ⟦ xs' ⟧ ≡ suc ⟦ xs ⟧

next-number-suc-NullBase : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ next-number-NullBase xs ¬max ⟧ ≡ suc ⟦ xs ⟧
next-number-suc-NullBase {d} {o} xs ¬max with NullBase-view d o
next-number-suc-NullBase {_} {_} xs       ¬max | AllZeros = contradiction (AllZeros-Maximum xs) ¬max
next-number-suc-NullBase {d} {o} xs       ¬max | Others bound with Greatest? (lsd xs)
next-number-suc-NullBase {d} {o} xs       ¬max | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ¬max
next-number-suc-NullBase {d} {o} (x ∙)    ¬max | Others bound | no ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o
    ≡⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Fin.toℕ x + o)
    ∎
next-number-suc-NullBase {d} {o} (x ∷ xs) ¬max | Others bound | no ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * zero
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * zero) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Fin.toℕ x + o + ⟦ xs ⟧ * zero)
    ∎

next-number-suc-Others-Abundant : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → (abundant : Abundant (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ⟦ next-number-Others xs ¬max d+o≥2 ⟧ ≡ suc ⟦ xs ⟧
next-number-suc-Others-Abundant {b} {d} {o} (x ∙) ¬max abundant d+o≥2 with Others-view-single b d o x
next-number-suc-Others-Abundant {b} {d} {o} (x ∙) ¬max abundant d+o≥2 | NeedNoCarry ¬greatest
    = proof
    where
        next : Num (suc b) (suc d) o
        next = digit+1 x ¬greatest ∙

        proof : ⟦ next ⟧ ≡ suc ⟦ _∙ {suc b} x ⟧
        proof = Digit-toℕ-digit+1 x ¬greatest
next-number-suc-Others-Abundant {b} {d} {o} (x ∙) ¬max abundant d+o≥2 | Gapped greatest gapped
    = proof
    where
        eq : (1 ⊔ o) * suc b ≡ suc d
        eq = IsPartialOrder.antisym isPartialOrder abundant gapped

        next : Num (suc b) (suc d) o
        next = z ∷ 1⊔o d o d+o≥2 ∙

        proof : ⟦ next ⟧ ≡ suc ⟦ _∙ {suc b} x ⟧
        proof = begin
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
next-number-suc-Others-Abundant {b} {d} {o} (x ∙) ¬max abundant d+o≥2 | ¬Gapped greatest ¬gapped
    = proof
    where
        lower-bound : (1 ⊔ o) * suc b > 0
        lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n

        upper-bound : (suc zero ⊔ o) * suc b ≤ suc (Fin.toℕ x + o)
        upper-bound = start
                (suc zero ⊔ o) * suc b
            ≤⟨ ≤-pred ¬gapped ⟩
                d
            ≈⟨ suc-injective (sym greatest) ⟩
                Fin.toℕ x
            ≤⟨ ≤-step (m≤m+n (Fin.toℕ x) o) ⟩
                suc (Fin.toℕ x + o)
            □
        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ 1⊔o d o d+o≥2 ∙

        proof : ⟦ next ⟧ ≡ suc ⟦ _∙ {suc b} x ⟧
        proof = begin
                Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + Digit-toℕ (1⊔o d o d+o≥2) o * suc b
            ≡⟨ cong₂ (λ v w → v + w * suc b) (Digit-toℕ-digit+1-n x greatest ((suc zero ⊔ o) * suc b) lower-bound abundant) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
                ((suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b) + (suc zero ⊔ o) * suc b)
            ≡⟨ m∸n+n≡m {suc (Fin.toℕ x + o)} {(suc zero ⊔ o) * suc b} upper-bound ⟩
                suc (Fin.toℕ x + o)
            ∎
next-number-suc-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max abundant d+o≥2 with Others-view x xs ¬max d+o≥2
next-number-suc-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max abundant d+o≥2 | NeedNoCarry ¬greatest
    = proof
    where
        next : Num (suc b) (suc d) o
        next = digit+1 x ¬greatest ∷ xs

        proof : ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
        proof = cong (λ w → w + ⟦ xs ⟧ * suc b) (Digit-toℕ-digit+1 x ¬greatest)

next-number-suc-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max abundant d+o≥2 | Gapped greatest gapped
    = proof
    where

        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = next-number-¬Maximum xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Others xs ¬max-xs d+o≥2

        ¬redundant : suc b ≥ suc d
        ¬redundant =
            start
                suc d
            ≤⟨ gapped ⟩
                (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
            ≈⟨ cong (λ w → (w ∸ ⟦ xs ⟧) * suc b) (next-number-suc-Others-Abundant xs ¬max-xs abundant d+o≥2) ⟩
                (suc ⟦ xs ⟧ ∸ ⟦ xs ⟧) * suc b
            ≈⟨ cong (λ w → w * suc b) (m+n∸n≡m 1 ⟦ xs ⟧) ⟩
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

        next : Num (suc b) (suc d) o
        next = z ∷ next-xs

        proof : ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
        proof =
            begin
                o + ⟦ next-xs ⟧ * suc b
            ≡⟨ cong (λ w → (o + w * suc b)) (next-number-suc-Others-Abundant xs ¬max-xs abundant d+o≥2) ⟩
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
next-number-suc-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max abundant d+o≥2 | ¬Gapped greatest ¬gapped
    = proof
    where

        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = next-number-¬Maximum xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Others xs ¬max-xs d+o≥2

        next-xs>xs : ⟦ next-xs ⟧ > ⟦ xs ⟧
        next-xs>xs = next-number-is-greater-Others xs ¬max-xs d+o≥2

        gap : ℕ
        gap = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b

        gap-lower-bound : gap > 0
        gap-lower-bound = (start
                1
            ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ xs ⟧))) ⟩
                suc (⟦ xs ⟧ ∸ ⟦ xs ⟧)
            ≈⟨ sym (+-∸-assoc 1 {⟦ xs ⟧} ≤-refl) ⟩
                suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
            ≤⟨ ∸-mono {suc ⟦ xs ⟧} {⟦ next-xs ⟧} {⟦ xs ⟧} (next-number-is-greater-Others xs ¬max-xs d+o≥2) ≤-refl ⟩
                ⟦ next-xs ⟧ ∸ ⟦ xs ⟧
            □) *-mono (s≤s {0} {b} z≤n)

        gap-upper-bound : gap ≤ suc d
        gap-upper-bound = <⇒≤ ¬gapped

        gap-upper-bound' : ⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b ≤ suc (Digit-toℕ x o)
        gap-upper-bound' =
            start
                ⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b
            ≈⟨ sym (*-distrib-∸ʳ (suc b) ⟦ next-xs ⟧ ⟦ xs ⟧) ⟩
                (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
            ≤⟨ gap-upper-bound ⟩
                suc d
            ≤⟨ m≤m+n (suc d) o ⟩
                suc d + o
            ≈⟨ cong (λ w → w + o) (sym greatest) ⟩
                suc (Digit-toℕ x o)
            □

        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest gap gap-lower-bound ∷ next-xs

        proof : ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
        proof =
            begin
                Digit-toℕ (digit+1-n x greatest gap gap-lower-bound) o + ⟦ next-xs ⟧ * suc b
            ≡⟨ cong (λ w → w + ⟦ next-xs ⟧ * suc b) (Digit-toℕ-digit+1-n x greatest gap gap-lower-bound gap-upper-bound) ⟩
                suc (Digit-toℕ x o) ∸ gap +  ⟦ next-xs ⟧ * suc b
            ≡⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + ⟦ next-xs ⟧ * suc b) (*-distrib-∸ʳ (suc b) ⟦ next-xs ⟧ ⟦ xs ⟧) ⟩
                suc (Digit-toℕ x o) ∸ (⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b) + ⟦ next-xs ⟧ * suc b
            ≡⟨ m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ xs ⟧ * suc b) (⟦ next-xs ⟧ * suc b) (*n-mono (suc b) (<⇒≤ next-xs>xs)) gap-upper-bound' ⟩
                suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
            ∎

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

next-number-suc-Others-Sparse : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → (¬greatest : ¬ (Greatest (lsd xs)))
    → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ⟦ next-number-Others xs ¬max d+o≥2 ⟧ ≡ suc ⟦ xs ⟧
next-number-suc-Others-Sparse {b} {d} {o} (x ∙) ¬max ¬greatest ¬abundant d+o≥2 with Others-view-single b d o x
next-number-suc-Others-Sparse {b} {d} {o} (x ∙) ¬max ¬greatest ¬abundant d+o≥2 | NeedNoCarry _
    = proof
    where
        next : Num (suc b) (suc d) o
        next = digit+1 x ¬greatest ∙

        proof : ⟦ next ⟧ ≡ suc ⟦ _∙ {suc b} x ⟧
        proof = Digit-toℕ-digit+1 x ¬greatest
next-number-suc-Others-Sparse (x ∙) ¬max ¬greatest ¬abundant d+o≥2 | Gapped greatest gapped = contradiction greatest ¬greatest
next-number-suc-Others-Sparse (x ∙) ¬max ¬greatest ¬abundant d+o≥2 | ¬Gapped greatest ¬gapped = contradiction greatest ¬greatest
next-number-suc-Others-Sparse {b} {d} {o} (x ∷ xs) ¬max ¬greatest ¬abundant d+o≥2 with Others-view x xs ¬max d+o≥2
next-number-suc-Others-Sparse {b} {d} {o} (x ∷ xs) ¬max ¬greatest ¬abundant d+o≥2 | NeedNoCarry _
    = proof
    where
        next : Num (suc b) (suc d) o
        next = digit+1 x ¬greatest ∷ xs

        proof : ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
        proof = cong (λ w → w + ⟦ xs ⟧ * suc b) (Digit-toℕ-digit+1 x ¬greatest)
next-number-suc-Others-Sparse (x ∷ xs) ¬max ¬greatest ¬abundant d+o≥2 | Gapped greatest gapped = contradiction greatest ¬greatest
next-number-suc-Others-Sparse (x ∷ xs) ¬max ¬greatest ¬abundant d+o≥2 | ¬Gapped greatest ¬gapped = contradiction greatest ¬greatest


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

next-number-suc-Others : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → (greatest : Greatest (lsd xs))
    → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ¬ (Incrementable xs)
-- next-number-suc-Others {b} {d} {o} xs ¬max greatest ¬abundant d+o≥2 (evidence , claim) = {!   !}
next-number-suc-Others {b} {d} {o} (x ∙) ¬max greatest ¬abundant d+o≥2 (evidence , claim) with Others-view-single b d o x
next-number-suc-Others {b} {d} {o} (x ∙) ¬max greatest ¬abundant d+o≥2 (evidence , claim) | NeedNoCarry ¬greatest = contradiction greatest ¬greatest
next-number-suc-Others {b} {d} {o} (x ∙) ¬max greatest ¬abundant d+o≥2 ((y ∙) , claim) | Gapped _ gapped = contradiction (m≡1+n⇒m>n claim) (>⇒≰ (s≤s (greatest-of-all o x y greatest)))
next-number-suc-Others {b} {d} {o} (x ∙) ¬max greatest ¬abundant d+o≥2 (y ∷ ys , claim) | Gapped _ gapped
    = {!   !}
    where
        next : Num (suc b) (suc d) o
        next = z ∷ 1⊔o d o d+o≥2 ∙

        ⟦next⟧>⟦evidence⟧ : ⟦ next ⟧ > ⟦ y ∷ ys ⟧
        ⟦next⟧>⟦evidence⟧ =
            start
                suc ⟦ y ∷ ys ⟧
            ≈⟨ cong suc claim ⟩
                suc (suc (Fin.toℕ x + o))
            ≈⟨ cong (λ w → suc w + o) greatest ⟩
                suc (suc (d + o))
            ≈⟨ +-comm (suc (suc d)) o ⟩
                o + suc (suc d)
            ≤⟨ n+-mono o (≰⇒> ¬abundant) ⟩
                o + (suc zero ⊔ o) * suc b
            ≈⟨ cong (λ w → o + w * suc b) (sym (Digit-toℕ-1⊔o d o d+o≥2)) ⟩
                o + Digit-toℕ (1⊔o d o d+o≥2) o * suc b
            □

        prop : ⟦ y ∷ ys ⟧ > ⟦ _∙ {suc b} x ⟧
        prop = m≡1+n⇒m>n claim

        ⟦next⟧≯⟦evidence⟧ : ⟦ next ⟧ ≤ ⟦ y ∷ ys ⟧
        ⟦next⟧≯⟦evidence⟧ = next-number-is-LUB-Others {! _∙ {suc b} {suc d} {o} x  !} (y ∷ ys) ¬max d+o≥2 prop -- next-number-is-LUB-Others {! x ∙  !} evidence ¬max d+o≥2 {!   !}

    -- = contradiction ⟦next⟧>⟦evidence⟧ (≤⇒≯ ⟦next⟧≯⟦evidence⟧)
    -- where
    --     next : Num (suc b) (suc d) o
    --     next = z ∷ 1⊔o d o d+o≥2 ∙
    --
    --     ⟦next⟧>⟦evidence⟧ : ⟦ next ⟧ > ⟦ y ∷ ys ⟧
    --     ⟦next⟧>⟦evidence⟧ =
    --         start
    --             suc ⟦ y ∷ ys ⟧
    --         ≈⟨ cong suc claim ⟩
    --             suc (suc (Fin.toℕ x + o))
    --         ≈⟨ cong (λ w → suc w + o) greatest ⟩
    --             suc (suc (d + o))
    --         ≈⟨ +-comm (suc (suc d)) o ⟩
    --             o + suc (suc d)
    --         ≤⟨ n+-mono o (≰⇒> ¬abundant) ⟩
    --             o + (suc zero ⊔ o) * suc b
    --         ≈⟨ cong (λ w → o + w * suc b) (sym (Digit-toℕ-1⊔o d o d+o≥2)) ⟩
    --             o + Digit-toℕ (1⊔o d o d+o≥2) o * suc b
    --         □
    --
    --     prop : ⟦ y ∷ ys ⟧ > ⟦ _∙ {suc b} x ⟧
    --     prop = m≡1+n⇒m>n claim
    --
    --     ⟦next⟧≯⟦evidence⟧ : ⟦ next ⟧ ≤ ⟦ y ∷ ys ⟧
    --     ⟦next⟧≯⟦evidence⟧ = temp x y ys ¬max d+o≥2 prop greatest gapped -- next-number-is-LUB-Others {! x ∙  !} evidence ¬max d+o≥2 {!   !}

next-number-suc-Others (x ∙) ¬max greatest ¬abundant d+o≥2 (evidence , claim) | ¬Gapped _ ¬gapped = contradiction (<⇒≤ ¬gapped) ¬abundant
next-number-suc-Others {b} {d} {o} (x ∷ xs) ¬max greatest ¬abundant d+o≥2 (evidence , claim) = {!   !}
    -- where
    --     next : Num (suc b) (suc d) o
    --     next = next-number-Others xs ¬max d+o≥2
    --
    --     ⟦next⟧>⟦evidence⟧ : ⟦ next ⟧ > ⟦ evidence ⟧
    --     ⟦next⟧>⟦evidence⟧ = {!   !}

data IncrementableCond : (b d o : ℕ) (xs : Num b d o) → Set where
    NullBase : ∀ {d o}
        → {xs : Num 0 (suc d) o}
        → (¬max : ¬ (Maximum xs))
        → IncrementableCond 0 (suc d) o xs
    Others-Abundant : ∀ {b d o}
        → {xs : Num (suc b) (suc d) o}
        → (¬max : ¬ (Maximum xs))
        → (abundant : Abundant (suc b) (suc d) o)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → IncrementableCond (suc b) (suc d) o xs
    Others-Sparse : ∀ {b d o}
        → {xs : Num (suc b) (suc d) o}
        → (¬max : ¬ (Maximum xs))
        → (¬greatest : ¬ (Greatest (lsd xs)))
        → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → IncrementableCond (suc b) (suc d) o xs

data NonIncrementableCond : (b d o : ℕ) (xs : Num b d o) → Set where
    Max : ∀ {b d o}
        → {xs : Num b d o}
        → (max : Maximum xs)
        → NonIncrementableCond b d o xs
    Others : ∀ {b d o}
        → {xs : Num (suc b) (suc d) o}
        → (¬max : ¬ (Maximum xs))
        → (greatest : Greatest (lsd xs))
        → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → NonIncrementableCond (suc b) (suc d) o xs

data IncrementableView : (b d o : ℕ) (xs : Num b d o) → Set where
    IsIncrementable : ∀ {b d o} {xs : Num b d o}
        → IncrementableCond b d o xs
        → IncrementableView b d o xs
    IsntIncrementable : ∀ {b d o} {xs : Num b d o}
        → NonIncrementableCond b d o xs
        → IncrementableView b d o xs

incrementableView : ∀ {b d o}
    → (xs : Num b d o)
    → IncrementableView b d o xs
incrementableView xs with Maximum? xs
incrementableView xs | yes max = IsntIncrementable (Max max)
incrementableView {b} {d} {o} xs | no ¬max with boundedView b d o
incrementableView xs | no ¬max | IsBounded (NullBase d o) = IsIncrementable (NullBase ¬max)
incrementableView xs | no ¬max | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) with Abundant? (suc b) (suc d) o
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) | yes abundant = IsIncrementable (Others-Abundant ¬max abundant d+o≥2)
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) | no ¬abundant with Greatest? (lsd xs)
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) | no ¬abundant | yes greatest = IsntIncrementable (Others ¬max greatest ¬abundant d+o≥2)
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) | no ¬abundant | no ¬greatest = IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant d+o≥2)
incrementableView xs | no ¬max | IsntBounded (NoDigits b o) = NoDigits-explode xs


Incrementable? : ∀ {b d o}
    → (xs : Num b d o)
    → Dec (Incrementable xs)
Incrementable? xs with incrementableView xs
Incrementable? xs | IsIncrementable (NullBase ¬max) = yes ((next-number-NullBase xs ¬max) , (next-number-suc-NullBase xs ¬max))
Incrementable? {suc b} {suc d} {o} xs | IsIncrementable (Others-Abundant ¬max abundant _) with boundedView (suc b) (suc d) o
Incrementable? {suc .b} {suc .0} xs | IsIncrementable (Others-Abundant ¬max abundant _) | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
Incrementable? {suc .b} {suc .d} xs | IsIncrementable (Others-Abundant ¬max abundant _) | IsntBounded (Others b d o d+o≥2) = yes ((next-number-Others xs ¬max d+o≥2) , next-number-suc-Others-Abundant xs ¬max abundant d+o≥2)
Incrementable? {suc b} {suc d} {o} xs | IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant _) with boundedView (suc b) (suc d) o
Incrementable? {suc .b} {suc .0} xs | IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant _) | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
Incrementable? {suc .b} {suc .d} xs | IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant _) | IsntBounded (Others b d o d+o≥2) = yes ((next-number-Others xs ¬max d+o≥2) , (next-number-suc-Others-Sparse xs ¬max ¬greatest ¬abundant d+o≥2))
Incrementable? xs | IsntIncrementable (Max max) = no (Maximum⇒¬Incrementable xs max)
Incrementable? xs | IsntIncrementable (Others ¬max greatest ¬abundant d+o≥2) = no {!   !}

increment : ∀ {b d o}
    → (xs : Num b d o)
    → (incr : True (Incrementable? xs))
    → Num b d o
increment xs incr = proj₁ (toWitness incr)

increment-next-number : ∀ {b d o}
    → (xs : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → (incr : True (Incrementable? xs))
    → increment xs incr ≡ next-number xs ¬max
increment-next-number xs ¬max incr with incrementableView xs
increment-next-number xs ¬max incr | IsIncrementable (NullBase _) = refl
increment-next-number {suc b} {suc d} {o} xs ¬max incr | IsIncrementable (Others-Abundant _ abundant _) with boundedView (suc b) (suc d) o
increment-next-number {suc .b} {suc .0} xs ¬max incr | IsIncrementable (Others-Abundant _ abundant _) | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
increment-next-number {suc .b} {suc .d} xs ¬max incr | IsIncrementable (Others-Abundant _ abundant _) | IsntBounded (Others b d o d+o≥2) = refl
increment-next-number {suc b} {suc d} {o} xs ¬max incr | IsIncrementable (Others-Sparse _ ¬greatest ¬abundant _) with boundedView (suc b) (suc d) o
increment-next-number {suc .b} {suc .0} xs ¬max incr | IsIncrementable (Others-Sparse _ ¬greatest ¬abundant _) | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
increment-next-number {suc .b} {suc .d} xs ¬max incr | IsIncrementable (Others-Sparse _ ¬greatest ¬abundant _) | IsntBounded (Others b d o d+o≥2) = refl
increment-next-number xs ¬max () | IsntIncrementable (Max _)
increment-next-number xs ¬max () | IsntIncrementable (Others _ _ _ _)


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
