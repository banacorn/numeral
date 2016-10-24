module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
open import Data.Num.Incrementable
-- open import Data.Num.Continuous

open import Data.Bool
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

subsume2 : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (gapped : suc (suc d) ≤ suc b)
    → suc (suc d) ≤ (⟦ next-number-Others xs (next-number-¬Maximum xs d+o≥2) d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
subsume2 {b} {d} {o} xs d+o≥2 gapped =
    start
        suc (suc d)
    ≤⟨ gapped ⟩
        suc b
    ≈⟨ sym (+-right-identity (suc b)) ⟩
        suc zero * suc b
    ≤⟨ *n-mono (suc b) (m≥n+o⇒m∸o≥n ⟦ next-number-Others xs (next-number-¬Maximum xs d+o≥2) d+o≥2 ⟧ (suc zero) ⟦ xs ⟧ (next-number-is-greater-Others xs (next-number-¬Maximum xs d+o≥2) d+o≥2)) ⟩
        (⟦ next-number-Others xs (next-number-¬Maximum xs d+o≥2) d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
    □

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

subsume-contra : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (¬gapped : suc (suc d) > (1 ⊔ o) * suc b)
    → suc (suc d) > (⟦ next-number-Others xs (next-number-¬Maximum xs d+o≥2) d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
subsume-contra {b} {d} {o} xs d+o≥2 ¬gapped = {!   !}
    -- start
    --     (⟦ next-number-Others xs (next-number-¬Maximum xs d+o≥2) d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
    -- ≤⟨ *n-mono (suc b) {! subsume  !} ⟩
    --     1 * suc b
    -- ≤⟨ *n-mono (suc b) (m≤m⊔n 1 o) ⟩
    --     (suc zero ⊔ o) * suc b
    -- ≤⟨ ≤-pred ¬gapped ⟩
    --     suc d
    -- □

-- subsume : ∀ {b d o}
--     → (xs : Num (suc b) (suc d) o)
--     → (d+o≥2 : 2 ≤ suc (d + o))
--     → (gapped : suc (suc d) ≤ (⟦ next-number-Others xs (next-number-¬Maximum xs d+o≥2) d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b)
--     → suc (suc d) ≤ (1 ⊔ o) * suc b
-- subsume {b} {d} {o} (x ∙) d+o≥2 gapped with Others-view-single b d o x
-- subsume {b} {d} {o} (x ∙) d+o≥2 gapped | NeedNoCarry ¬greatest =
--     start
--         suc (suc d)
--     ≤⟨ gapped ⟩
--         (Digit-toℕ (digit+1 x ¬greatest) o ∸ Digit-toℕ x o) * suc b
--     ≤⟨ *n-mono (suc b) $
--         start
--             Digit-toℕ (digit+1 x ¬greatest) o ∸ Digit-toℕ x o
--         ≈⟨ cong (λ w → w ∸ Digit-toℕ x o) (next-number-Others-NeedNoCarry-Single {b} x ¬greatest) ⟩
--             suc (Fin.toℕ x + o) ∸ (Fin.toℕ x + o)
--         ≈⟨ m+n∸n≡m (suc zero) (Fin.toℕ x + o) ⟩
--             suc zero
--         ≤⟨ m≤m⊔n 1 o ⟩
--             suc zero ⊔ o
--         □
--     ⟩
--         (suc zero ⊔ o) * suc b
--     □
-- subsume {b} {d} {o} (x ∙) d+o≥2 _ | Gapped greatest gapped = gapped
-- subsume {b} {d} {o} (x ∙) d+o≥2 gapped | ¬Gapped greatest ¬gapped =
--     start
--         suc (suc d)
--     ≤⟨ gapped ⟩
--         (⟦ digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ 1⊔o d o d+o≥2 ∙ ⟧ ∸ Digit-toℕ x o) * suc b
--     ≤⟨ *n-mono (suc b) $
--         start
--             ⟦ digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ 1⊔o d o d+o≥2 ∙ ⟧ ∸ Digit-toℕ x o
--         ≈⟨ cong (λ w → w ∸ Digit-toℕ x o) (next-number-suc-Others-¬Gapped-Single x greatest d+o≥2 ¬gapped) ⟩
--             suc (Fin.toℕ x + o) ∸ (Fin.toℕ x + o)
--         ≈⟨ m+n∸n≡m (suc zero) (Fin.toℕ x + o) ⟩
--             suc zero
--         ≤⟨ m≤m⊔n 1 o ⟩
--             suc zero ⊔ o
--         □
--     ⟩
--         (suc zero ⊔ o) * suc b
--     □
--     where
--         lower-bound : (1 ⊔ o) * suc b > 0
--         lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n
-- subsume {b} {d} {o} (x ∷ xs) d+o≥2 gapped with Others-view x xs (next-number-¬Maximum (x ∷ xs) d+o≥2) d+o≥2
-- subsume {b} {d} {o} (x ∷ xs) d+o≥2 gapped | NeedNoCarry ¬greatest =
--     start
--         suc (suc d)
--     ≤⟨ gapped ⟩
--         (⟦ digit+1 x ¬greatest ∷ xs ⟧ ∸ ⟦ x ∷ xs ⟧) * suc b
--     ≤⟨ *n-mono (suc b) $
--         start
--             ⟦ digit+1 x ¬greatest ∷ xs ⟧ ∸ ⟦ x ∷ xs ⟧
--         ≈⟨ cong (λ w → w ∸ ⟦ x ∷ xs ⟧) (next-number-Others-NeedNoCarry x xs ¬greatest) ⟩
--             suc ⟦ x ∷ xs ⟧ ∸ ⟦ x ∷ xs ⟧
--         ≈⟨ m+n∸n≡m (suc zero) ⟦ x ∷ xs ⟧ ⟩
--             suc zero
--         ≤⟨ m≤m⊔n 1 o ⟩
--             suc zero ⊔ o
--         □
--     ⟩
--         (suc zero ⊔ o) * suc b
--     □
-- subsume {b} {d} {o} (x ∷ xs) d+o≥2 gapped | Gapped greatest gapped-xs = subsume xs d+o≥2 gapped-xs
-- subsume {b} {d} {o} (x ∷ xs) d+o≥2 gapped | ¬Gapped greatest ¬gapped =
--     start
--         suc (suc d)
--     ≤⟨ gapped ⟩
--         (⟦ digit+1-n x greatest gap lower-bound ∷ next-xs ⟧ ∸ ⟦ x ∷ xs ⟧) * suc b
--     ≤⟨ *n-mono (suc b) $
--         start
--             ⟦ digit+1-n x greatest gap lower-bound ∷ next-xs ⟧ ∸ ⟦ x ∷ xs ⟧
--         ≈⟨ cong (λ w → w ∸ ⟦ x ∷ xs ⟧) (next-number-suc-Others-¬Gapped x xs greatest d+o≥2 (s≤s ¬gapped)) ⟩
--             suc ⟦ x ∷ xs ⟧ ∸ ⟦ x ∷ xs ⟧
--         ≈⟨ m+n∸n≡m (suc zero) ⟦ x ∷ xs ⟧ ⟩
--             suc zero
--         ≤⟨ m≤m⊔n 1 o ⟩
--             suc zero ⊔ o
--         □
--     ⟩
--         (suc zero ⊔ o) * suc b
--     □
--     where
--         ¬max-xs : ¬ (Maximum xs)
--         ¬max-xs = next-number-¬Maximum xs d+o≥2
--
--         next-xs : Num (suc b) (suc d) o
--         next-xs = next-number-Others xs ¬max-xs d+o≥2
--
--         gap : ℕ
--         gap = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
--
--         lower-bound : gap > 0
--         lower-bound = (start
--                 1
--             ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ xs ⟧))) ⟩
--                 suc (⟦ xs ⟧ ∸ ⟦ xs ⟧)
--             ≈⟨ sym (+-∸-assoc 1 {⟦ xs ⟧} ≤-refl) ⟩
--                 suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
--             ≤⟨ ∸-mono {suc ⟦ xs ⟧} {⟦ next-xs ⟧} {⟦ xs ⟧} (next-number-is-greater-Others xs ¬max-xs d+o≥2) ≤-refl ⟩
--                 ⟦ next-xs ⟧ ∸ ⟦ xs ⟧
--             □) *-mono (s≤s {0} {b} z≤n)
--
--         next : Num (suc b) (suc d) o
--         next = digit+1-n x greatest gap lower-bound ∷ next-xs

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
