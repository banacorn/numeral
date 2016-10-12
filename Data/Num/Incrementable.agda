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

Incrementable : ∀ {b d o} → (xs : Num b d o) → (xs! : ¬ (Null xs)) → Set
Incrementable {b} {d} {o} xs xs! = Σ[ xs' ∈ Num b d o ] Σ[ xs'! ∈ ¬ (Null xs') ] ⟦ xs' ⟧ xs'! ≡ suc (⟦ xs ⟧ xs!)

m≡1+n⇒m>n : ∀ {m n} → m ≡ suc n → m > n
m≡1+n⇒m>n {zero}  {n}  ()
m≡1+n⇒m>n {suc m} {.m} refl = s≤s ≤-refl

Maximum⇒¬Incrementable : ∀ {b d o}
    → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → (max : Maximum xs xs!)
    → ¬ (Incrementable xs xs!)
Maximum⇒¬Incrementable xs xs! max (evidence , evidence! , claim)
    = contradiction (max evidence evidence!) (>⇒≰ (m≡1+n⇒m>n claim))

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
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → Dec (Incrementable xs xs!)
Incrementable-Base≡0 {d} {o} xs            xs! ¬max with Base≡0-view d o
Incrementable-Base≡0         xs            xs! ¬max | HasOnly0 = contradiction (HasOnly0-Maximum xs xs!) ¬max
Incrementable-Base≡0         ∙             xs! ¬max | Others bound = contradiction tt xs!
Incrementable-Base≡0         (x ∷ xs)      xs! ¬max | Others bound with Greatest? x
Incrementable-Base≡0         (x ∷ xs)      xs! ¬max | Others bound | yes greatest = contradiction (Base≡0-Maximum x xs greatest) ¬max
Incrementable-Base≡0 {d} {o} (x ∷ ∙)       xs! ¬max | Others bound | no ¬greatest = yes (digit+1 x ¬greatest ∷ ∙ , id , prop)
    where
        prop : ⟦ digit+1 x ¬greatest ∷ ∙ {0} ⟧  ≡ suc ⟦ x ∷ ∙ {0} ⟧
        prop = begin
                Digit-toℕ (digit+1 x ¬greatest) o
            ≡⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
                suc ⟦ x ∷ ∙ {0} ⟧
            ∎
Incrementable-Base≡0 {d} {o} (x ∷ x' ∷ xs) xs! ¬max | Others bound | no ¬greatest = yes (digit+1 x ¬greatest ∷ x' ∷ xs , id , prop)
    where
        prop : ⟦ digit+1 x ¬greatest ∷ (x' ∷ xs) ⟧  ≡ suc ⟦ x ∷ (x' ∷ xs) ⟧
        prop = begin
                Digit-toℕ (digit+1 x ¬greatest) o + ⟦ x' ∷ xs ⟧ * 0
            ≡⟨ cong (λ w → w + ⟦ x' ∷ xs ⟧ * 0) (Digit-toℕ-digit+1 x ¬greatest) ⟩
                suc ⟦ x ∷ (x' ∷ xs) ⟧
            ∎

Incrementable-d+o≥2 :  ∀ {b d o}
    → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → Dec (Incrementable xs xs!)
Incrementable-d+o≥2 xs xs! ¬max with cmp (⟦ next-number xs xs! ¬max ⟧ (next-number-¬Null xs xs! ¬max) ∸ ⟦ xs ⟧ xs!) 1
Incrementable-d+o≥2 xs xs! ¬max | tri< p ¬q ¬r = contradiction p (>⇒≰ (s≤s ¬p))
    where
         next  = next-number xs xs! ¬max
         next! = next-number-¬Null xs xs! ¬max
         ¬p : ⟦ next ⟧ next! ∸ ⟦ xs ⟧ xs! > 0
         ¬p = +n-mono-inverse (⟦ xs ⟧ xs!) $
            start
                1 + ⟦ xs ⟧ xs!
            ≤⟨ next-number-is-greater xs xs! ¬max ⟩
                (⟦ next ⟧ next!)
            ≈⟨ sym (m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs xs! ¬max))) ⟩
                ⟦ next ⟧ next! ∸ ⟦ xs ⟧ xs! + ⟦ xs ⟧ xs!
            □
Incrementable-d+o≥2 xs xs! ¬max | tri≈ ¬p q ¬r = yes (next-number xs xs! ¬max , next-number-¬Null xs xs! ¬max , prop)
    where
        next  = next-number xs xs! ¬max
        next! = next-number-¬Null xs xs! ¬max
        prop : ⟦ next ⟧ next! ≡ suc (⟦ xs ⟧ xs!)
        prop =
            begin
                (⟦ next ⟧ next!)
            ≡⟨ sym (m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs xs! ¬max))) ⟩
                ⟦ next ⟧ next! ∸ (⟦ xs ⟧ xs!) + (⟦ xs ⟧ xs!)
            ≡⟨ cong (λ w → w + ⟦ xs ⟧ xs!) q ⟩
                suc (⟦ xs ⟧ xs!)
            ∎
Incrementable-d+o≥2 xs xs! ¬max | tri> ¬p ¬q r = no prop
    where
        next  = next-number xs xs! ¬max
        next! = next-number-¬Null xs xs! ¬max
        prop : ¬ Incrementable xs xs!
        prop (evidence , evidence! , claim) = contradiction ⟦next⟧>⟦evidence⟧ ⟦next⟧≯⟦evidence⟧
            where
                ⟦next⟧>⟦evidence⟧ : ⟦ next ⟧ next! > ⟦ evidence ⟧ evidence!
                ⟦next⟧>⟦evidence⟧ =
                    start
                        suc (⟦ evidence ⟧ evidence!)
                    ≈⟨ cong suc claim ⟩
                        2 + (⟦ xs ⟧ xs!)
                    ≤⟨ +n-mono (⟦ xs ⟧ xs!) r ⟩
                        ⟦ next ⟧ next! ∸ (⟦ xs ⟧ xs!) + (⟦ xs ⟧ xs!)
                    ≈⟨ m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs xs! ¬max)) ⟩
                        ⟦ next ⟧ next!
                    □
                ⟦next⟧≯⟦evidence⟧ : ⟦ next ⟧ next! ≯ ⟦ evidence ⟧ evidence!
                ⟦next⟧≯⟦evidence⟧ = ≤⇒≯ (next-number-is-LUB xs evidence xs! evidence! ¬max (m≡1+n⇒m>n claim))

Incrementable? : ∀ {b d o}
    → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → Dec (Incrementable xs xs!)
Incrementable? {b} {d} {o} xs xs! with Maximum? xs xs!
Incrementable? {b} {d} {o} xs xs! | yes max = no (Maximum⇒¬Incrementable xs xs! max)
Incrementable? {b} {d} {o} xs xs! | no ¬max with boundedView b d o
Incrementable? xs xs! | no ¬max | IsBounded (Base≡0 d o) = Incrementable-Base≡0 xs xs! ¬max
Incrementable? xs xs! | no ¬max | IsBounded (HasOnly0 b) = contradiction (HasOnly0-Maximum xs xs!) ¬max
Incrementable? xs xs! | no ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = Incrementable-d+o≥2 xs xs! ¬max
Incrementable? xs xs! | no ¬max | IsntBounded (HasNoDigit b o) = HasNoDigit-explode xs xs!

increment : ∀ {b d o}
    → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → Incrementable xs xs!
    → Num b d o
increment xs xs! (next , next! , claim) = next

increment-¬Null : ∀ {b d o}
    → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → (incr : Incrementable xs xs!)
    → ¬ (Null (increment xs xs! incr))
increment-¬Null xs xs! (next , next! , prop) = next!

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
