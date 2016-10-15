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

Incrementable-Base≡0 :  ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → Dec (Incrementable xs)
Incrementable-Base≡0 {d} {o} xs            ¬max with Base≡0-view d o
Incrementable-Base≡0 xs ¬max | HasOnly0 = contradiction (HasOnly0-Maximum xs) ¬max
Incrementable-Base≡0 xs ¬max | Others bound with Greatest? (lsd xs)
Incrementable-Base≡0 xs ¬max | Others bound | yes greatest = contradiction (Base≡0-Maximum xs greatest) ¬max
Incrementable-Base≡0 (x ∙) ¬max | Others bound | no ¬greatest = yes (digit+1 x ¬greatest ∙ , Digit-toℕ-digit+1 x ¬greatest )
Incrementable-Base≡0 (x ∷ xs) ¬max | Others bound | no ¬greatest = yes (digit+1 x ¬greatest ∷ xs , cong (λ w → w + ⟦ xs ⟧ * 0) (Digit-toℕ-digit+1 x ¬greatest))

Incrementable-d+o≥2 :  ∀ {b d o}
    → (xs : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → Dec (Incrementable xs)
Incrementable-d+o≥2 xs ¬max with cmp (⟦ next-number xs ¬max ⟧ ∸ ⟦ xs ⟧) 1
Incrementable-d+o≥2 xs ¬max | tri< p ¬q ¬r = contradiction p (>⇒≰ (s≤s ¬p))
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
Incrementable-d+o≥2 xs ¬max | tri≈ ¬p q ¬r = yes (next-number xs ¬max , prop)
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
Incrementable-d+o≥2 xs ¬max | tri> ¬p ¬q r = no prop
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
Incrementable? xs | no ¬max | IsBounded (Base≡0 d o) = Incrementable-Base≡0 xs ¬max
Incrementable? xs | no ¬max | IsBounded (HasOnly0 b) = contradiction (HasOnly0-Maximum xs) ¬max
Incrementable? xs | no ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = Incrementable-d+o≥2 xs ¬max
Incrementable? xs | no ¬max | IsntBounded (HasNoDigit b o) = HasNoDigit-explode xs

increment : ∀ {b d o}
    → (xs : Num b d o)
    → Incrementable xs
    → Num b d o
increment xs (next , claim) = next

Continuous : ∀ b d o → Set
Continuous b d o = Σ[ n ∈ ℕ ] ((xs : Num b d o) → (xs! : ¬ (Null xs)) → ⟦ xs ⟧ xs! ≥ n → Incrementable xs xs!)

StartsFrom0-¬Maximum : ∀ {b d}
    → d ≥ b
    → (xs : Num b d 0) → (xs! : ¬ (Null xs))
    → ¬ (Maximum xs xs!)
StartsFrom0-¬Maximum {b} {d} cond xs xs! with boundedView b d 0
StartsFrom0-¬Maximum cond₁ xs xs! | IsBounded (Base≡0 d .0) = {!   !}
StartsFrom0-¬Maximum cond₁ xs xs! | IsBounded (HasOnly0 b) = {!   !}
StartsFrom0-¬Maximum cond₁ xs xs! | IsntBounded cond = {!   !}

-- StartsFrom0-Continuous : ∀ {b d}
--     → d ≥ b
--     → (xs : Num b d 0) → (xs! : ¬ (Null xs))
--     → ⟦ xs ⟧ xs! ≥ 0
--     → Incrementable xs xs!
-- StartsFrom0-Continuous cond xs xs! prop with Maximum? xs xs!
-- StartsFrom0-Continuous cond xs xs! prop | yes max = contradiction max ¬max
--     where   ¬max : ¬ (Maximum xs xs!)
--             ¬max = {!   !}
-- StartsFrom0-Continuous cond xs xs! prop | no ¬max = {!   !}

data ContinuousCond : ℕ → ℕ → ℕ → Set where
    continuousCond : ∀ {b} {d} {o}
        → NonBoundedCond b d o
        → (prop : d ≥ (1 ⊔ o) * b)
        → ContinuousCond b d o

StartsFrom0-Continuous : ∀ {b d}
    → ContinuousCond b d 0
    → Continuous b d 0
StartsFrom0-Continuous (continuousCond (Digit+Offset≥2 b d .0 d+o≥2) prop) = 0 , {!   !}
StartsFrom0-Continuous (continuousCond (HasNoDigit b .0) prop) = {!   !}

ContinuousCond⇒Continuous : ∀ {b d o}
    → ContinuousCond b d o
    → Continuous b d o
ContinuousCond⇒Continuous {b} {d} {zero} cond = {!   !}
ContinuousCond⇒Continuous {b} {d} {suc zero} cond = {!   !}
ContinuousCond⇒Continuous {b} {d} {suc (suc o)} cond = {!   !}


-- d≥[1⊔o]*b⇒Continuous : ∀ {b d o} → d ≥ (1 ⊔ o) * b → Continuous b d o
-- d≥[1⊔o]*b⇒Continuous {b} {d} {zero} cond = 0 , StartsFrom0-Continuous (≤-trans (reflexive (sym (+-right-identity b))) cond)
-- d≥[1⊔o]*b⇒Continuous {b} {d} {suc zero} cond = {!   !}
-- d≥[1⊔o]*b⇒Continuous {b} {d} {suc (suc o)} cond = {!o   !}


-- -- begin
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ∎
--
-- -- start
-- --     {!   !}
-- -- ≤⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≤⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≤⟨ {!   !} ⟩
-- --     {!   !}
-- -- □
