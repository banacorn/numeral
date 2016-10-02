module Data.Num.Maximum where

open import Data.Num.Core
open import Data.Num.Bounded

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
--

-- data MaximumCond : ∀ {b} {d} {o} → Num b d o → Set where
--     ≡Bound : ∀ {b d o} (xs : Num b d o) → MaximumCond xs
--
-- data NonMaximumCond : ∀ {b} {d} {o} → Num b d o → Set where
--

Maximum?-lemma-1 : ∀ {b d o}
    → (xs : Num b d o)
    → (max : Num b d o)
    → Maximum max
    → toℕ max ≢ toℕ xs
    → Maximum xs
    → ⊥
Maximum?-lemma-1 xs max claim p xs-be-maximum
    = contradiction ⟦xs⟧≥⟦max⟧ ⟦xs⟧≱⟦max⟧
    where   ⟦xs⟧≥⟦max⟧ : toℕ xs ≥ toℕ max
            ⟦xs⟧≥⟦max⟧ = xs-be-maximum max
            ⟦xs⟧≱⟦max⟧ : toℕ xs ≱ toℕ max
            ⟦xs⟧≱⟦max⟧ = <⇒≱ $ ≤∧≢⇒< (claim xs) (λ x → p (sym x))

Maximum? : ∀ {b d o}
    → (xs : Num b d o)
    → Dec (Maximum xs)
Maximum? {b} {d} {o} xs with boundedView b d o
Maximum? xs | IsBounded cond with BoundedCond⇒Bounded cond
Maximum? xs | IsBounded cond | max , claim with toℕ max ≟ toℕ xs
Maximum? xs | IsBounded cond | max , claim | yes p rewrite p = yes claim
Maximum? xs | IsBounded cond | max , claim | no ¬p = no (Maximum?-lemma-1 xs max claim ¬p)
Maximum? xs | IsntBounded cond = no (¬Bounded⇒¬Maximum (NonBoundedCond⇒¬Bounded cond) xs)


next-number-lemma-3 : ∀ {b d o}
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → (¬Maximum : ¬ (Maximum (x ∷ xs)))
    → (greatest : Greatest x)
    → suc d + o ≥ 2
    → Maximum xs
    → ⊥
next-number-lemma-3 {b} {d} {o} x xs ¬max greatest d+o≥2 claim = contradiction p ¬p
    where   p : toℕ xs ≥ toℕ (x ∷ xs)
            p = claim (x ∷ xs)
            ¬p : toℕ xs ≱ toℕ (x ∷ xs)
            ¬p = <⇒≱ $
                start
                    suc (toℕ xs)
                ≤⟨ reflexive (cong suc (sym (*-right-identity (toℕ xs)))) ⟩
                    suc (toℕ xs * suc zero)
                ≤⟨ s≤s (n*-mono (toℕ xs) (s≤s z≤n)) ⟩
                    suc (toℕ xs * suc b)
                ≤⟨ +n-mono (toℕ xs * suc b) (≤-pred d+o≥2) ⟩
                    d + o + toℕ xs * suc b
                ≤⟨ reflexive (cong (λ w → w + toℕ xs * suc b) (sym (toℕ-greatest x greatest))) ⟩
                    Digit-toℕ x o + toℕ xs * suc b
                □


next-number-lemma-6 : ∀ d o
    → (xs : Num 0 (suc d) o)
    → 1 > d + o
    → Maximum {0} {suc d} {o} xs
next-number-lemma-6 zero zero xs p ∙ = z≤n
next-number-lemma-6 zero zero xs p (z ∷ ys) =
    start
        toℕ ys * zero
    ≤⟨ reflexive (*-right-zero (toℕ ys)) ⟩
        zero
    ≤⟨ z≤n ⟩
        toℕ xs
    □
next-number-lemma-6 zero zero xs p (s () ∷ ys)
next-number-lemma-6 zero (suc o) xs (s≤s ())
next-number-lemma-6 (suc d) o xs (s≤s ())


data NextView-0 : ℕ → ℕ → Set where
    HasOnly:0 :                                  NextView-0 0 0
    Others : ∀ {d o} → (bound : d + o ≥ 1 ⊔ o) → NextView-0 d o

nextView-0 : ∀ d o → NextView-0 d o
nextView-0 zero    zero     = HasOnly:0
nextView-0 zero    (suc o)  = Others (s≤s ≤-refl)
nextView-0 (suc d) zero     = Others (s≤s z≤n)
nextView-0 (suc d) (suc o)  = Others (m≤n+m (suc o) (suc d))

next-number-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → ¬ (Maximum xs)
    → Num 0 (suc d) o
next-number-Base≡0 {d} {o} xs ¬max with nextView-0 d o
next-number-Base≡0 xs ¬max | HasOnly:0 = contradiction (next-number-lemma-6 zero zero xs (s≤s z≤n)) ¬max
next-number-Base≡0 {d} {o} ∙ ¬max | Others bound = Digit-fromℕ {d} {o} (1 ⊔ o) bound ∷ ∙
next-number-Base≡0 (x ∷ xs) ¬max | Others bound with Greatest? x
next-number-Base≡0 (x ∷ xs) ¬max | Others bound | yes greatest = contradiction (Base≡0-lemma x xs greatest) ¬max
next-number-Base≡0 (x ∷ xs) ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∷ xs

next-number : ∀ {b d o}
    → (xs : Num b d o)
    → ¬ (Maximum xs)
    → Num b d o
next-number {b} {d} {o} xs ¬max with boundedView b d o
next-number xs ¬max | IsBounded (Base≡0 d o) = next-number-Base≡0 xs ¬max
next-number xs ¬max | IsBounded (HasNoDigit b o) = {!   !}
next-number xs ¬max | IsBounded (HasOnly:0 b) = {!   !}
next-number xs ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = {!   !}




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


next-number-is-greater-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → toℕ (next-number-Base≡0 xs ¬max) > toℕ xs
next-number-is-greater-Base≡0 {d} {o} xs ¬max with nextView-0 d o
next-number-is-greater-Base≡0 xs ¬max | HasOnly:0 = contradiction (next-number-lemma-6 zero zero xs (s≤s z≤n)) ¬max
next-number-is-greater-Base≡0 {d} {o} ∙ ¬max | Others bound =
    start
        1
    ≤⟨ m≤m⊔n 1 o ⟩
        1 ⊔ o
    ≤⟨ reflexive $
        begin
            1 ⊔ o
        ≡⟨ sym (+-right-identity (1 ⊔ o)) ⟩
            1 ⊔ o + 0
        ≡⟨ cong (λ x → x + 0) (sym (Digit-toℕ-fromℕ {d} {o} bound $ start
                o
            ≤⟨ m≤m⊔n o 1 ⟩
                o ⊔ 1
            ≤⟨ reflexive (⊔-comm o 1) ⟩
                1 ⊔ o
            □))
        ⟩
            Digit-toℕ {suc d} (Digit-fromℕ {d} {o} (1 ⊔ o) bound) o + 0
        ∎
    ⟩
        Digit-toℕ {suc d} (Digit-fromℕ {d} {o} (1 ⊔ o) bound) o + 0
    □
next-number-is-greater-Base≡0 (x ∷ xs) ¬max | Others bound with Greatest? x
next-number-is-greater-Base≡0 (x ∷ xs) ¬max | Others bound | yes greatest = contradiction (Base≡0-lemma x xs greatest) ¬max
next-number-is-greater-Base≡0 (x ∷ xs) ¬max | Others bound | no ¬greatest = ∷ns-mono-strict x (digit+1 x ¬greatest) xs xs refl (reflexive (sym (digit+1-lemma x ¬greatest)))


next-number-is-greater : ∀ {b d o}
    → (xs : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → toℕ (next-number xs ¬max) > toℕ xs
next-number-is-greater {b} {d} {o} xs ¬max with boundedView b d o
next-number-is-greater xs ¬max | IsBounded (Base≡0 d o) = next-number-is-greater-Base≡0 xs ¬max
next-number-is-greater xs ¬max | IsBounded (HasNoDigit b o) = {!   !}
next-number-is-greater xs ¬max | IsBounded (HasOnly:0 b) = {!   !}
next-number-is-greater xs ¬max | IsntBounded cond = {!   !}


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
