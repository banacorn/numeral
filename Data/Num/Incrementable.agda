module Data.Num.Incrementable where

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

------------------------------------------------------------------------
-- a number is incrementable if there exists some n' : Num b d o such that ⟦ n' ⟧ℕ ≡ suc ⟦ n ⟧ℕ

Incrementable : ∀ {b d o} → (xs : Num b d o) → Set
Incrementable {b} {d} {o} xs = Σ[ xs' ∈ Num b d o ] ⟦ xs' ⟧ ≡ suc ⟦ xs ⟧

m≡1+n⇒m>n : ∀ {m n} → m ≡ suc n → m > n
m≡1+n⇒m>n {zero}  {n}  ()
m≡1+n⇒m>n {suc m} {.m} refl = s≤s ≤-refl

Maximum⇒¬Incrementable : ∀ {b d o}
    → (xs : Num b d o)
    → (max : Maximum xs)
    → ¬ (Incrementable xs)
Maximum⇒¬Incrementable xs max (evidence , claim)
    = contradiction (max evidence) (>⇒≰ (m≡1+n⇒m>n claim))

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

Incrementable-NullBase :  ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → Dec (Incrementable xs)
Incrementable-NullBase {d} {o} xs            ¬max with NullBase-view d o
Incrementable-NullBase xs ¬max | AllZeros = contradiction (AllZeros-Maximum xs) ¬max
Incrementable-NullBase xs ¬max | Others bound with Greatest? (lsd xs)
Incrementable-NullBase xs ¬max | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ¬max
Incrementable-NullBase (x ∙) ¬max | Others bound | no ¬greatest = yes (digit+1 x ¬greatest ∙ , Digit-toℕ-digit+1 x ¬greatest )
Incrementable-NullBase (x ∷ xs) ¬max | Others bound | no ¬greatest = yes (digit+1 x ¬greatest ∷ xs , cong (λ w → w + ⟦ xs ⟧ * 0) (Digit-toℕ-digit+1 x ¬greatest))

Incrementable-Others :  ∀ {b d o}
    → (xs : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → Dec (Incrementable xs)
Incrementable-Others xs ¬max with cmp (⟦ next-number xs ¬max ⟧ ∸ ⟦ xs ⟧) 1
Incrementable-Others xs ¬max | tri< p ¬q ¬r = contradiction p (>⇒≰ (s≤s ¬p))
    where
         next  = next-number xs ¬max
         ¬p : ⟦ next ⟧ ∸ ⟦ xs ⟧ > 0
         ¬p = +n-mono-inverse ⟦ xs ⟧ $
            start
                1 + ⟦ xs ⟧
            ≤⟨ next-number-is-greater xs ¬max ⟩
                (⟦ next ⟧)
            ≈⟨ sym (m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs ¬max))) ⟩
                ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
            □
Incrementable-Others xs ¬max | tri≈ ¬p q ¬r = yes (next-number xs ¬max , prop)
    where
        next  = next-number xs ¬max
        prop : ⟦ next ⟧ ≡ suc ⟦ xs ⟧
        prop =
            begin
                (⟦ next ⟧)
            ≡⟨ sym (m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs ¬max))) ⟩
                ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
            ≡⟨ cong (λ w → w + ⟦ xs ⟧) q ⟩
                suc ⟦ xs ⟧
            ∎
Incrementable-Others xs ¬max | tri> ¬p ¬q r = no prop
    where
        next  = next-number xs ¬max
        prop : ¬ Incrementable xs
        prop (evidence , claim) = contradiction ⟦next⟧>⟦evidence⟧ ⟦next⟧≯⟦evidence⟧
            where
                ⟦next⟧>⟦evidence⟧ : ⟦ next ⟧ > ⟦ evidence ⟧
                ⟦next⟧>⟦evidence⟧ =
                    start
                        suc ⟦ evidence ⟧
                    ≈⟨ cong suc claim ⟩
                        2 + ⟦ xs ⟧
                    ≤⟨ +n-mono ⟦ xs ⟧ r ⟩
                        ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
                    ≈⟨ m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs ¬max)) ⟩
                        ⟦ next ⟧
                    □
                ⟦next⟧≯⟦evidence⟧ : ⟦ next ⟧ ≯ ⟦ evidence ⟧
                ⟦next⟧≯⟦evidence⟧ = ≤⇒≯ (next-number-is-LUB xs evidence ¬max (m≡1+n⇒m>n claim))

Incrementable? : ∀ {b d o}
    → (xs : Num b d o)
    → Dec (Incrementable xs)
Incrementable? {b} {d} {o} xs with Maximum? xs
Incrementable? {b} {d} {o} xs | yes max = no (Maximum⇒¬Incrementable xs max)
Incrementable? {b} {d} {o} xs | no ¬max with boundedView b d o
Incrementable? xs | no ¬max | IsBounded (NullBase d o) = Incrementable-NullBase xs ¬max
Incrementable? xs | no ¬max | IsBounded (AllZeros b) = contradiction (AllZeros-Maximum xs) ¬max
Incrementable? xs | no ¬max | IsntBounded (Others b d o d+o≥2) = Incrementable-Others xs ¬max
Incrementable? xs | no ¬max | IsntBounded (NoDigits b o) = NoDigits-explode xs

increment : ∀ {b d o}
    → (xs : Num b d o)
    → Incrementable xs
    → Num b d o
increment xs (next , claim) = next

Continuous : ∀ b d o → Set
Continuous b d o = Σ[ n ∈ ℕ ] ((xs : Num b d o) → ⟦ xs ⟧ ≥ n → Incrementable xs)


data ContinuousCond : ℕ → ℕ → ℕ → Set where
    continuousCond : ∀ {b} {d} {o}
        → NonBoundedCond b d o
        → (prop : d ≥ (1 ⊔ o) * b)
        → ContinuousCond b d o

Continuous-Others-StartsFrom0-¬Maximum : ∀ {b d}
    → suc (b + 0) ≤ suc d
    → 2 ≤ suc (d + 0)
    → (xs : Num (suc b) (suc d) 0)
    → ¬ (Maximum xs)
Continuous-Others-StartsFrom0-¬Maximum {b} {d} prop d+o≥2 xs with boundedView (suc b) (suc d) 0
Continuous-Others-StartsFrom0-¬Maximum prop d+o≥2    xs | IsBounded cond with Maximum? xs
Continuous-Others-StartsFrom0-¬Maximum prop (s≤s ()) xs | IsBounded (AllZeros b) | yes max
Continuous-Others-StartsFrom0-¬Maximum prop d+o≥2    xs | IsBounded cond | no ¬max = ¬max
Continuous-Others-StartsFrom0-¬Maximum prop d+o≥2    xs | IsntBounded cond = ¬Bounded⇒¬Maximum xs (NonBoundedCond⇒¬Bounded cond)

Continuous-Others-StartsFrom0 : ∀ {b d}
    → suc (b + 0) ≤ suc d
    → 2 ≤ suc (d + 0)
    → (xs : Num (suc b) (suc d) 0)
    → ⟦ xs ⟧ ≥ 0
    → Incrementable xs
Continuous-Others-StartsFrom0 prop d+o≥2 xs _ with cmp (⟦ next-number xs (Continuous-Others-StartsFrom0-¬Maximum prop d+o≥2 xs) ⟧ ∸ ⟦ xs ⟧) 1
Continuous-Others-StartsFrom0 prop d+o≥2 xs _ | tri< p ¬q ¬r = contradiction p (>⇒≰ (s≤s ¬p))
    where
        ¬max = Continuous-Others-StartsFrom0-¬Maximum prop d+o≥2 xs
        next = next-number xs ¬max
        ¬p : ⟦ next ⟧ ∸ ⟦ xs ⟧ > 0
        ¬p = +n-mono-inverse ⟦ xs ⟧ $
            start
                1 + ⟦ xs ⟧
            ≤⟨ next-number-is-greater xs ¬max ⟩
                (⟦ next ⟧)
            ≈⟨ sym (m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs ¬max))) ⟩
                ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
            □
Continuous-Others-StartsFrom0 prop d+o≥2 xs _ | tri≈ ¬p q ¬r = (next-number xs ¬max) , proof
    where
        ¬max = Continuous-Others-StartsFrom0-¬Maximum prop d+o≥2 xs
        next  = next-number xs ¬max
        proof : ⟦ next ⟧ ≡ suc ⟦ xs ⟧
        proof =
            begin
                (⟦ next ⟧)
            ≡⟨ sym (m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs ¬max))) ⟩
                ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
            ≡⟨ cong (λ w → w + ⟦ xs ⟧) q ⟩
                suc ⟦ xs ⟧
            ∎
Continuous-Others-StartsFrom0 prop d+o≥2 xs _ | tri> ¬p ¬q r = {!   !}

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

-- Continuous-Others-StartsFrom0-lemma : ∀ {b d}
--     → (redundant : suc (b + 0) ≤ suc d)
--     → (2≤d+o : 2 ≤ suc (d + 0))
--     → (xs : Num (suc b) (suc d) 0)
--     → let
--         ¬max = Continuous-Others-StartsFrom0-¬Maximum redundant 2≤d+o xs
--         next  = next-number xs ¬max
--       in ⟦ next ⟧ ∸ ⟦ xs ⟧ ≤ 2
-- Continuous-Others-StartsFrom0-lemma {b} {d} redundant 2≤d+o xs with boundedView (suc b) (suc d) 0
-- Continuous-Others-StartsFrom0-lemma redundant (s≤s ()) xs | IsBounded (AllZeros b)
-- Continuous-Others-StartsFrom0-lemma redundant 2≤d+o (x ∙) | IsntBounded (Others b d .0 d+o≥2) with Greatest? x
-- Continuous-Others-StartsFrom0-lemma redundant 2≤d+o (x ∙) | IsntBounded (Others b d _ d+o≥2) | yes greatest with suc d ≤? suc (b + 0)
-- Continuous-Others-StartsFrom0-lemma redundant 2≤d+o (x ∙) | IsntBounded (Others b d _ d+o≥2) | yes greatest | yes gapped =
--     let
--         b≡d : suc b + 0 ≡ suc d
--         b≡d = IsPartialOrder.antisym isPartialOrder redundant gapped
--     in
--     start
--         ⟦ z ∷ 1⊔o (suc d) 0 (≤-step $ 2≤d+o) ∙ ⟧ ∸ (Fin.toℕ x + zero)
--     ≈⟨ refl ⟩
--         Digit-toℕ (1⊔o (suc d) 0 (≤-step $ 2≤d+o)) 0 * suc b ∸ (Fin.toℕ x + zero)
--     ≈⟨ cong (λ w → w * suc b ∸ (Fin.toℕ x + zero)) (Digit-toℕ-1⊔o (suc b) zero (s≤s (s≤s z≤n))) ⟩
--         suc (b + zero) ∸ (Fin.toℕ x + zero)
--     ≈⟨ cong (λ w → w ∸ (Fin.toℕ x + zero)) b≡d ⟩
--         suc d ∸ (Fin.toℕ x + zero)
--     ≈⟨ cong (λ w → w ∸ (Fin.toℕ x + zero)) (sym greatest) ⟩
--         suc (Fin.toℕ x) ∸ (Fin.toℕ x + zero)
--     ≤⟨ {!   !} ⟩
--         {!   !}
--     ≤⟨ {!   !} ⟩
--         2
--     □
-- Continuous-Others-StartsFrom0-lemma redundant 2≤d+o (x ∙) | IsntBounded (Others b d _ d+o≥2) | yes greatest | no ¬gapped = {!   !}
-- Continuous-Others-StartsFrom0-lemma redundant 2≤d+o (x ∙) | IsntBounded (Others b d _ d+o≥2) | no ¬greatest = {!   !}
-- Continuous-Others-StartsFrom0-lemma redundant 2≤d+o (x ∷ xs) | IsntBounded (Others b d .0 d+o≥2) = {!   !}
    -- where
    --     ¬max = Continuous-Others-StartsFrom0-¬Maximum prop d+o≥2 xs
    --     next  = next-number xs ¬max
    --     ¬r : 2 ≰ ⟦ next ⟧ ∸ ⟦ xs ⟧
    --     ¬r = >⇒≰ $ {!   !}
        -- proof : ¬ Incrementable xs
        -- proof (evidence , claim) = contradiction ⟦next⟧>⟦evidence⟧ ⟦next⟧≯⟦evidence⟧
        --     where
        --         ⟦next⟧>⟦evidence⟧ : ⟦ next ⟧ > ⟦ evidence ⟧
        --         ⟦next⟧>⟦evidence⟧ =
        --             start
        --                 suc ⟦ evidence ⟧
        --             ≈⟨ cong suc claim ⟩
        --                 2 + ⟦ xs ⟧
        --             ≤⟨ +n-mono ⟦ xs ⟧ r ⟩
        --                 ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
        --             ≈⟨ m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs ¬max)) ⟩
        --                 ⟦ next ⟧
        --             □
        --         ⟦next⟧≯⟦evidence⟧ : ⟦ next ⟧ ≯ ⟦ evidence ⟧
        --         ⟦next⟧≯⟦evidence⟧ = ≤⇒≯ (next-number-is-LUB xs evidence ¬max (m≡1+n⇒m>n claim))

Continuous-NoDigits : ∀ {b o}
    → (1 ⊔ o) * b ≤ 0
    → Continuous b 0 o
Continuous-NoDigits prop = 0 , (λ xs x → NoDigits-explode xs)
--     →

-- Continuous (suc b) (suc d) (suc zero)
ContinuousCond⇒Continuous : ∀ {b d o}
    → ContinuousCond b d o
    → Continuous b d o
ContinuousCond⇒Continuous (continuousCond (Others b d zero d+o≥2) prop) = 0 , Continuous-Others-StartsFrom0 prop d+o≥2
ContinuousCond⇒Continuous (continuousCond (Others b d (suc zero) d+o≥2) prop) = {!   !}
ContinuousCond⇒Continuous (continuousCond (Others b d (suc (suc o)) d+o≥2) prop) = {!   !}
ContinuousCond⇒Continuous (continuousCond (NoDigits b d) prop) = Continuous-NoDigits prop

-- d≥[1⊔o]*b⇒Continuous : ∀ {b d o} → d ≥ (1 ⊔ o) * b → Continuous b d o
-- d≥[1⊔o]*b⇒Continuous {b} {d} {zero} cond = 0 , StartsFrom0-Continuous (≤-trans (reflexive (sym (+-right-identity b))) cond)
-- d≥[1⊔o]*b⇒Continuous {b} {d} {suc zero} cond = {!   !}
-- d≥[1⊔o]*b⇒Continuous {b} {d} {suc (suc o)} cond = {!o   !}


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
