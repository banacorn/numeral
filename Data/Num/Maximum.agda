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



data NextView-0 : ℕ → ℕ → Set where
    HasOnly:0 :                                  NextView-0 0 0
    Others : ∀ {d o} → (bound : d + o ≥ 1 ⊔ o) → NextView-0 d o

nextView-0 : ∀ d o → NextView-0 d o
nextView-0 zero    zero     = HasOnly:0
nextView-0 zero    (suc o)  = Others (s≤s ≤-refl)
nextView-0 (suc d) zero     = Others (s≤s z≤n)
nextView-0 (suc d) (suc o)  = Others (m≤n+m (suc o) (suc d))

next-number-Base≡0-lemma-1 : ∀ d o
    → (xs : Num 0 (suc d) o)
    → 1 > d + o
    → Maximum {0} {suc d} {o} xs
next-number-Base≡0-lemma-1 zero zero xs p ∙ = z≤n
next-number-Base≡0-lemma-1 zero zero xs p (z ∷ ys) =
    start
        toℕ ys * zero
    ≤⟨ reflexive (*-right-zero (toℕ ys)) ⟩
        zero
    ≤⟨ z≤n ⟩
        toℕ xs
    □
next-number-Base≡0-lemma-1 zero zero xs p (s () ∷ ys)
next-number-Base≡0-lemma-1 zero (suc o) xs (s≤s ())
next-number-Base≡0-lemma-1 (suc d) o xs (s≤s ())


next-number-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → ¬ (Maximum xs)
    → Num 0 (suc d) o
next-number-Base≡0 {d} {o} xs ¬max with nextView-0 d o
next-number-Base≡0 xs         ¬max | HasOnly:0    = contradiction (next-number-Base≡0-lemma-1 zero zero xs (s≤s z≤n)) ¬max
next-number-Base≡0 {d} {o} ∙  ¬max | Others bound = Digit-fromℕ {d} (1 ⊔ o) o bound ∷ ∙
next-number-Base≡0 (x ∷ xs)   ¬max | Others bound with Greatest? x
next-number-Base≡0 (x ∷ xs)   ¬max | Others bound | yes greatest = contradiction (Base≡0-lemma x xs greatest) ¬max
next-number-Base≡0 (x ∷ xs)   ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∷ xs

next-number-HasNoDigit : ∀ {b o}
    → (xs : Num b 0 o)
    → ¬ (Maximum xs)
    → Num b 0 o
next-number-HasNoDigit {b} {o} ∙         ¬max = contradiction (HasNoDigit-lemma b o) ¬max
next-number-HasNoDigit         (() ∷ xs) ¬max

next-number-HasOnly:0 : ∀ {b}
    → (xs : Num (suc b) 1 0)
    → ¬ (Maximum xs)
    → Num (suc b) 1 0
next-number-HasOnly:0 {b} xs ¬max = contradiction (HasOnly:0-lemma (suc b) xs) ¬max

next-number-Digit+Offset≥2-lemma-1 : ∀ m n → 2 ≤ suc m + n → m + n ≥ 1 ⊔ n
next-number-Digit+Offset≥2-lemma-1 m zero    q = ≤-pred q
next-number-Digit+Offset≥2-lemma-1 m (suc n) q = m≤n+m (suc n) m


next-number-Digit+Offset≥2-lemma-2 : ∀ {b d o}
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → (¬Maximum : ¬ (Maximum (x ∷ xs)))
    → (greatest : Greatest x)
    → suc d + o ≥ 2
    → Maximum xs
    → ⊥
next-number-Digit+Offset≥2-lemma-2 {b} {d} {o} x xs ¬max greatest d+o≥2 claim = contradiction p ¬p
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


mutual
    next-number-Digit+Offset≥2 : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → ¬ (Maximum xs)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Num (suc b) (suc d) o
    next-number-Digit+Offset≥2 {_} {d} {o} ∙        ¬max p = Digit-fromℕ {d} (1 ⊔ o) o (next-number-Digit+Offset≥2-lemma-1 d o p) ∷ ∙
    next-number-Digit+Offset≥2 {_} {d} {o} (x ∷ xs) ¬max p with Greatest? x
    next-number-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest
        with Redundant? ((toℕ (next-number-Digit+Offset≥2 xs (next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest p) p) ∸ toℕ xs) * suc b) (suc d)
    next-number-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest | yes redundant =
        let
            ¬max-xs = next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest p
            next-xs = next-number-Digit+Offset≥2 xs ¬max-xs p
            gap = (toℕ next-xs ∸ toℕ xs) * suc b
            gap>0 = (start
                    1
                ≤⟨ s≤s (reflexive (sym (n∸n≡0 (toℕ xs)))) ⟩
                    suc (toℕ xs ∸ toℕ xs)
                ≤⟨ reflexive (sym (+-∸-assoc 1 {toℕ xs} ≤-refl)) ⟩
                    suc (toℕ xs) ∸ toℕ xs
                ≤⟨ ∸-mono {suc (toℕ xs)} {toℕ next-xs} {toℕ xs} (next-number-is-greater-Digit+Offset≥2 xs ¬max-xs p) ≤-refl ⟩
                    toℕ next-xs ∸ toℕ xs
                □) *-mono (s≤s z≤n)
        in
        digit+1-b x gap gap>0 redundant greatest ∷ next-xs
    next-number-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest | no ¬redundant
        = z ∷ next-number-Digit+Offset≥2 xs (next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest p) p
    next-number-Digit+Offset≥2 {_} {d} {o} (x ∷ xs) ¬max p | no ¬greatest = digit+1 x ¬greatest ∷ xs


    next-number-is-greater-Digit+Offset≥2 : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (¬max : ¬ (Maximum xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → toℕ (next-number-Digit+Offset≥2 xs ¬max d+o≥2) > toℕ xs
    next-number-is-greater-Digit+Offset≥2 {b} {d} {o}     ∙ ¬max p =
        start
            suc zero
        ≤⟨ m≤m⊔n (suc zero) o ⟩
            suc zero ⊔ o
        ≤⟨ reflexive (sym (+-right-identity (suc zero ⊔ o))) ⟩
            suc zero ⊔ o + zero
        ≤⟨ +n-mono 0 (reflexive (sym (Digit-toℕ-fromℕ {d} (suc zero ⊔ o) (next-number-Digit+Offset≥2-lemma-1 d o p) $
            start
                o
            ≤⟨ m≤m⊔n o (suc zero) ⟩
                o ⊔ suc zero
            ≤⟨ reflexive (⊔-comm o (suc zero)) ⟩
                suc zero ⊔ o
            □)))
        ⟩
            Digit-toℕ (Digit-fromℕ {d} (1 ⊔ o) o (next-number-Digit+Offset≥2-lemma-1 d o p)) o + zero
        □
    next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p with Greatest? x
    next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest
        with Redundant? ((toℕ (next-number-Digit+Offset≥2 xs (next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest p) p) ∸ toℕ xs) * suc b) (suc d)
    next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest | yes redundant =
        let
            ¬max-xs : ¬ (Maximum xs)
            ¬max-xs = next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest p

            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Digit+Offset≥2 xs (next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest p) p

            gap : ℕ
            gap = (toℕ next-xs ∸ toℕ xs) * suc b

            gap>0 : gap > 0
            gap>0 = (start
                    1
                ≤⟨ s≤s (reflexive (sym (n∸n≡0 (toℕ xs)))) ⟩
                    suc (toℕ xs ∸ toℕ xs)
                ≤⟨ reflexive (sym (+-∸-assoc 1 {toℕ xs} ≤-refl)) ⟩
                    suc (toℕ xs) ∸ toℕ xs
                ≤⟨ ∸-mono {suc (toℕ xs)} {toℕ next-xs} {toℕ xs} (next-number-is-greater-Digit+Offset≥2 xs ¬max-xs p) ≤-refl ⟩
                    toℕ next-xs ∸ toℕ xs
                □) *-mono (s≤s z≤n)

            next-xs>xs : toℕ next-xs > toℕ xs
            next-xs>xs = next-number-is-greater-Digit+Offset≥2 xs ¬max-xs p

            next-xs-upper-bound : toℕ next-xs * suc b ∸ toℕ xs * suc b ≤ suc (Digit-toℕ x o)
            next-xs-upper-bound =
                start
                    toℕ next-xs * suc b ∸ toℕ xs * suc b
                ≤⟨ reflexive (sym (*-distrib-∸ʳ (suc b) (toℕ next-xs) (toℕ xs))) ⟩
                    (toℕ next-xs ∸ toℕ xs) * suc b
                ≤⟨ ≤-pred redundant ⟩
                    d
                ≤⟨ m≤m+n d (suc o) ⟩
                    d + suc o
                ≤⟨ reflexive (+-suc d o) ⟩
                    suc (d + o)
                ≤⟨ s≤s $ reflexive (sym (toℕ-greatest x greatest)) ⟩
                    suc (Fin.toℕ x + o)
                □
            next-xs-lower-bound : toℕ xs * suc b ≤ toℕ next-xs * suc b
            next-xs-lower-bound = *n-mono (suc b) (≤-pred (≤-step (next-number-is-greater-Digit+Offset≥2 xs ¬max-xs p)))

        in reflexive $ sym $ begin
                toℕ (digit+1-b x gap gap>0 redundant greatest ∷ next-xs)
            ≡⟨ refl ⟩
                Digit-toℕ (digit+1-b x gap gap>0 redundant greatest) o + toℕ next-xs * suc b
            ≡⟨ cong (λ w → w + toℕ next-xs * suc b) (Digit-toℕ-digit+1-b x gap gap>0 redundant greatest) ⟩
                suc (Digit-toℕ x o) ∸ (toℕ next-xs ∸ toℕ xs) * suc b + toℕ next-xs * suc b
            ≡⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + toℕ next-xs * suc b) (*-distrib-∸ʳ (suc b) (toℕ next-xs) (toℕ xs)) ⟩
                suc (Digit-toℕ x o) ∸ (toℕ next-xs * suc b ∸ toℕ xs * suc b) + toℕ next-xs * suc b
            ≡⟨ m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (toℕ xs * suc b) (toℕ next-xs * suc b) next-xs-lower-bound next-xs-upper-bound ⟩
                suc (toℕ (x ∷ xs))
            ∎

    next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest | no ¬redundant =
        let
            ¬max-xs : ¬ (Maximum xs)
            ¬max-xs = next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest p

            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Digit+Offset≥2 xs ¬max-xs p

            next-xs>xs : toℕ next-xs > toℕ xs
            next-xs>xs = next-number-is-greater-Digit+Offset≥2 xs ¬max-xs p

            prop : d < ((toℕ next-xs ∸ toℕ xs) * suc b)
            prop = ≤-pred $ ≰⇒> ¬redundant
        in
        start
            suc (toℕ (x ∷ xs))
        ≤⟨ ≤-refl ⟩
            suc (Digit-toℕ x o) + toℕ xs * suc b
        ≤⟨ reflexive (cong (λ w → suc w + toℕ xs * suc b) (toℕ-greatest x greatest)) ⟩
            suc d + o + toℕ xs * suc b
        ≤⟨ reflexive (+-assoc (suc d) o (toℕ xs * suc b)) ⟩
            suc d + (o + toℕ xs * suc b)
        ≤⟨ reflexive (a+[b+c]≡b+[a+c] (suc d) o (toℕ xs * suc b)) ⟩
            o + (suc d + toℕ xs * suc b)
        ≤⟨ ≤-refl ⟩
            o + (suc d + toℕ xs * suc b)
        ≤⟨ n+-mono o (+n-mono (toℕ xs * suc b) prop) ⟩
            o + ((toℕ next-xs ∸ toℕ xs) * suc b + toℕ xs * suc b)
        ≤⟨ reflexive (cong (λ w → o + w) (sym (distribʳ-*-+ (suc b) (toℕ next-xs ∸ toℕ xs) (toℕ xs)))) ⟩
            o + (toℕ next-xs ∸ toℕ xs + toℕ xs) * suc b
        ≤⟨ reflexive (cong (λ w → o + w * suc b) (m∸n+n≡m (≤-pred $ ≤-step next-xs>xs))) ⟩
            o + toℕ next-xs * suc b
        ≤⟨ ≤-refl ⟩
            toℕ (z ∷ next-xs)
        □
    next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | no ¬greatest
        = +n-mono (toℕ xs * suc b) (reflexive (sym (Digit-toℕ-digit+1 x ¬greatest)))


next-number : ∀ {b d o}
    → (xs : Num b d o)
    → ¬ (Maximum xs)
    → Num b d o
next-number {b} {d} {o} xs ¬max with boundedView b d o
next-number xs ¬max | IsBounded (Base≡0 d o)    = next-number-Base≡0 xs ¬max
next-number xs ¬max | IsBounded (HasNoDigit b o) = next-number-HasNoDigit xs ¬max
next-number xs ¬max | IsBounded (HasOnly:0 b) = next-number-HasOnly:0 xs ¬max
next-number xs ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-Digit+Offset≥2 xs ¬max d+o≥2

next-number-is-greater-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → toℕ (next-number-Base≡0 xs ¬max) > toℕ xs
next-number-is-greater-Base≡0 {d} {o} xs ¬max with nextView-0 d o
next-number-is-greater-Base≡0 xs ¬max | HasOnly:0 = contradiction (next-number-Base≡0-lemma-1 zero zero xs (s≤s z≤n)) ¬max
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
        ≡⟨ cong (λ x → x + 0) (sym (Digit-toℕ-fromℕ {d} {o} (suc zero ⊔ o) bound $ start
                o
            ≤⟨ m≤m⊔n o 1 ⟩
                o ⊔ 1
            ≤⟨ reflexive (⊔-comm o 1) ⟩
                1 ⊔ o
            □))
        ⟩
            Digit-toℕ {suc d} (Digit-fromℕ {d} (1 ⊔ o) o bound) o + 0
        ∎
    ⟩
        Digit-toℕ {suc d} (Digit-fromℕ {d} (1 ⊔ o) o bound) o + 0
    □
next-number-is-greater-Base≡0 (x ∷ xs) ¬max | Others bound with Greatest? x
next-number-is-greater-Base≡0 (x ∷ xs) ¬max | Others bound | yes greatest = contradiction (Base≡0-lemma x xs greatest) ¬max
next-number-is-greater-Base≡0 (x ∷ xs) ¬max | Others bound | no ¬greatest = ∷ns-mono-strict x (digit+1 x ¬greatest) xs xs refl (reflexive (sym (Digit-toℕ-digit+1 x ¬greatest)))


next-number-is-greater-HasNoDigit : ∀ {b o}
    → (xs : Num b 0 o)
    → (¬max : ¬ (Maximum xs))
    → toℕ (next-number-HasNoDigit xs ¬max) > toℕ xs
next-number-is-greater-HasNoDigit {b} {o} ∙         ¬max = contradiction (HasNoDigit-lemma b o) ¬max
next-number-is-greater-HasNoDigit         (() ∷ xs) ¬max

next-number-is-greater-HasOnly:0 : ∀ {b}
    → (xs : Num (suc b) 1 0)
    → (¬max : ¬ (Maximum xs))
    → toℕ (next-number-HasOnly:0 xs ¬max) > toℕ xs
next-number-is-greater-HasOnly:0 {b} xs ¬max = contradiction (HasOnly:0-lemma (suc b) xs) ¬max


next-number-is-greater : ∀ {b d o}
    → (xs : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → toℕ (next-number xs ¬max) > toℕ xs
next-number-is-greater {b} {d} {o} xs ¬max with boundedView b d o
next-number-is-greater xs ¬max | IsBounded (Base≡0 d o) = next-number-is-greater-Base≡0 xs ¬max
next-number-is-greater xs ¬max | IsBounded (HasNoDigit b o) = next-number-is-greater-HasNoDigit xs ¬max
next-number-is-greater xs ¬max | IsBounded (HasOnly:0 b) = next-number-is-greater-HasOnly:0 xs ¬max
next-number-is-greater xs ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-is-greater-Digit+Offset≥2 xs ¬max d+o≥2


next-number-is-LUB-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (ys : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → toℕ ys > toℕ xs
    → toℕ ys ≥ toℕ (next-number-Base≡0 xs ¬max)
next-number-is-LUB-Base≡0 {d} {o} xs ys ¬max prop with nextView-0 d o
next-number-is-LUB-Base≡0 {0} {0} xs ys ¬max prop | HasOnly:0 = contradiction (next-number-Base≡0-lemma-1 zero zero xs (s≤s z≤n)) ¬max
next-number-is-LUB-Base≡0         ∙  ∙  ¬max ()   | Others bound
next-number-is-LUB-Base≡0 {d} {0} ∙ (y ∷ ys) ¬max prop | Others bound =
    start
        Digit-toℕ (Digit-fromℕ {d} 1 0 bound) 0 + 0
    ≤⟨ +n-mono 0 (reflexive (Digit-toℕ-fromℕ {d} {0} (suc zero) bound z≤n)) ⟩
        1
    ≤⟨ prop ⟩
        Fin.toℕ y + 0 + toℕ ys * 0
    □
next-number-is-LUB-Base≡0 {d} {suc o} ∙ (y ∷ ys) ¬max prop | Others bound =
    start
        Digit-toℕ (Digit-fromℕ (suc o) (suc o) bound) (suc o) + 0
    ≤⟨ +n-mono 0 (reflexive (Digit-toℕ-fromℕ {d} (suc o) bound ≤-refl)) ⟩
        suc o + 0
    ≤⟨ +n-mono 0 (m≤n+m (suc o) (Fin.toℕ y)) ⟩
        Digit-toℕ y (suc o) + zero
    ≤⟨ reflexive (cong (λ w → Digit-toℕ y (suc o) + w) (sym (*-right-zero (toℕ ys)))) ⟩
        Digit-toℕ y (suc o) + toℕ ys * zero
    □
next-number-is-LUB-Base≡0 (x ∷ xs) ∙        ¬max ()   | Others bound
next-number-is-LUB-Base≡0 {d} {o} (x ∷ xs) (y ∷ ys) ¬max prop | Others bound with Greatest? x
next-number-is-LUB-Base≡0 {d} {o} (x ∷ xs) (y ∷ ys) ¬max prop | Others bound | yes greatest = contradiction (Base≡0-lemma x xs greatest) ¬max
next-number-is-LUB-Base≡0 {d} {o} (x ∷ xs) (y ∷ ys) ¬max prop | Others bound | no ¬greatest =
    start
        Digit-toℕ (digit+1 x ¬greatest) o + toℕ xs * 0
    ≤⟨ +n-mono (toℕ xs * 0) (reflexive (Digit-toℕ-digit+1 x ¬greatest)) ⟩
        suc (toℕ (x ∷ xs))
    ≤⟨ prop ⟩
        toℕ (y ∷ ys)
    □




next-number-is-LUB-HasNoDigit : ∀ {b o}
    → (xs : Num b 0 o)
    → (ys : Num b 0 o)
    → (¬max : ¬ (Maximum xs))
    → toℕ ys ≥ toℕ (next-number-HasNoDigit xs ¬max)
next-number-is-LUB-HasNoDigit {b} {o} ∙         ys ¬max = contradiction (HasNoDigit-lemma b o) ¬max
next-number-is-LUB-HasNoDigit         (() ∷ xs) ys ¬max

next-number-is-LUB-Digit+Offset≥2 : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (ys : Num (suc b) (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → toℕ ys > toℕ xs
    → toℕ ys ≥ toℕ (next-number-Digit+Offset≥2 xs ¬max d+o≥2)
next-number-is-LUB-Digit+Offset≥2 ∙ ∙ ¬max d+o≥2 ()
next-number-is-LUB-Digit+Offset≥2 {b} {d} {zero} ∙ (y ∷ ys) ¬max d+o≥2 prop =
    start
        Digit-toℕ (Digit-fromℕ {d} (suc zero) zero (≤-pred d+o≥2)) 0 + 0
    ≤⟨ +n-mono 0 (reflexive (Digit-toℕ-fromℕ {d} 1 (≤-pred d+o≥2) z≤n)) ⟩
        suc zero
    ≤⟨ prop ⟩
        toℕ (y ∷ ys)
    □
next-number-is-LUB-Digit+Offset≥2 {b} {d} {suc o} ∙ (y ∷ ys) ¬max d+o≥2 prop =
    start
        Digit-toℕ (Digit-fromℕ {d} (suc o) (suc o) (next-number-Digit+Offset≥2-lemma-1 d (suc o) d+o≥2)) (suc o) + zero
    ≤⟨ +n-mono 0 (reflexive (Digit-toℕ-fromℕ {d} {suc o} (suc o) (m≤n+m (suc o) d) ≤-refl)) ⟩
        suc o + 0
    ≤⟨ (m≤n+m (suc o) (Fin.toℕ y)) +-mono z≤n ⟩
        Digit-toℕ y (suc o) + toℕ ys * suc b
    ≤⟨ ≤-refl ⟩
        toℕ (y ∷ ys)
    □
next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ∙ ¬max d+o≥2 ()
next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop with Greatest? x
next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | yes greatest
    with Redundant? ((toℕ (next-number-Digit+Offset≥2 xs (next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest d+o≥2) d+o≥2) ∸ toℕ xs) * suc b) (suc d)
next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | yes greatest | yes redundant =
    let

        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Digit+Offset≥2 xs ¬max-xs d+o≥2

        gap : ℕ
        gap = (toℕ next-xs ∸ toℕ xs) * suc b

        gap>0 : gap > 0
        gap>0 = (start
                1
            ≤⟨ s≤s (reflexive (sym (n∸n≡0 (toℕ xs)))) ⟩
                suc (toℕ xs ∸ toℕ xs)
            ≤⟨ reflexive (sym (+-∸-assoc 1 {toℕ xs} ≤-refl)) ⟩
                suc (toℕ xs) ∸ toℕ xs
            ≤⟨ ∸-mono {suc (toℕ xs)} {toℕ next-xs} {toℕ xs} (next-number-is-greater-Digit+Offset≥2 xs ¬max-xs d+o≥2) ≤-refl ⟩
                toℕ next-xs ∸ toℕ xs
            □) *-mono (s≤s z≤n)

        next-xs>xs : toℕ next-xs > toℕ xs
        next-xs>xs = next-number-is-greater-Digit+Offset≥2 xs ¬max-xs d+o≥2

        next-xs-upper-bound : toℕ next-xs * suc b ∸ toℕ xs * suc b ≤ suc (Digit-toℕ x o)
        next-xs-upper-bound =
            start
                toℕ next-xs * suc b ∸ toℕ xs * suc b
            ≤⟨ reflexive (sym (*-distrib-∸ʳ (suc b) (toℕ next-xs) (toℕ xs))) ⟩
                (toℕ next-xs ∸ toℕ xs) * suc b
            ≤⟨ ≤-pred redundant ⟩
                d
            ≤⟨ m≤m+n d (suc o) ⟩
                d + suc o
            ≤⟨ reflexive (+-suc d o) ⟩
                suc (d + o)
            ≤⟨ s≤s $ reflexive (sym (toℕ-greatest x greatest)) ⟩
                suc (Fin.toℕ x + o)
            □
        next-xs-lower-bound : toℕ xs * suc b ≤ toℕ next-xs * suc b
        next-xs-lower-bound = *n-mono (suc b) (≤-pred (≤-step (next-number-is-greater-Digit+Offset≥2 xs ¬max-xs d+o≥2)))

    in start
        Digit-toℕ (digit+1-b x gap gap>0 redundant greatest) o + toℕ next-xs * suc b
    ≤⟨ +n-mono (toℕ next-xs * suc b) (reflexive (Digit-toℕ-digit+1-b x gap gap>0 redundant greatest)) ⟩
        suc (Digit-toℕ x o) ∸ gap + toℕ next-xs * suc b
    ≤⟨ reflexive (cong (λ w → suc (Digit-toℕ x o) ∸ w + toℕ next-xs * suc b) (*-distrib-∸ʳ (suc b) (toℕ next-xs) (toℕ xs))) ⟩
        suc (Digit-toℕ x o) ∸ (toℕ next-xs * suc b ∸ toℕ xs * suc b) + toℕ next-xs * suc b
    ≤⟨ reflexive (m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (toℕ xs * suc b) (toℕ next-xs * suc b) next-xs-lower-bound next-xs-upper-bound) ⟩
        suc (Digit-toℕ x o) +  toℕ xs * suc b
    ≤⟨ prop ⟩
        toℕ (y ∷ ys)
    □

next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | yes greatest | no ¬redundant =
    let
        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Digit+Offset≥2 xs ¬max-xs d+o≥2

        ⟦ys⟧>⟦xs⟧ : toℕ ys > toℕ xs
        ⟦ys⟧>⟦xs⟧ = tail-mono-strict x y xs ys greatest prop

        ⟦ys⟧≥⟦next-xs⟧ : toℕ ys ≥ toℕ next-xs
        ⟦ys⟧≥⟦next-xs⟧ = next-number-is-LUB-Digit+Offset≥2 xs ys ¬max-xs d+o≥2 ⟦ys⟧>⟦xs⟧
    in
    start
        toℕ (z ∷ next-xs)
    ≤⟨ ≤-refl ⟩
        o + toℕ next-xs * suc b
    ≤⟨ m≤n+m o (Fin.toℕ y) +-mono (*n-mono (suc b) ⟦ys⟧≥⟦next-xs⟧) ⟩
        Digit-toℕ y o + toℕ ys * suc b
    ≤⟨ ≤-refl ⟩
        toℕ (y ∷ ys)
    □

next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | no ¬greatest =
    start
        toℕ (digit+1 x ¬greatest ∷ xs)
    ≤⟨ ≤-refl ⟩
        Digit-toℕ (digit+1 x ¬greatest) o + toℕ xs * suc b
    ≤⟨ +n-mono (toℕ xs * suc b) (reflexive (Digit-toℕ-digit+1 x ¬greatest)) ⟩
        suc (Fin.toℕ x + o + toℕ xs * suc b)
    ≤⟨ prop ⟩
        Fin.toℕ y + o + toℕ ys * suc b
    ≤⟨ ≤-refl ⟩
        toℕ (y ∷ ys)
    □

next-number-is-LUB : ∀ {b d o}
    → (xs : Num b d o)
    → (ys : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → toℕ ys > toℕ xs
    → toℕ ys ≥ toℕ (next-number xs ¬max)
next-number-is-LUB {b} {d} {o} xs ys ¬max prop with boundedView b d o
next-number-is-LUB xs ys ¬max prop | IsBounded (Base≡0 d o) = next-number-is-LUB-Base≡0 xs ys ¬max prop
next-number-is-LUB xs ys ¬max prop | IsBounded (HasNoDigit b o) = next-number-is-LUB-HasNoDigit xs ys ¬max
next-number-is-LUB xs ys ¬max prop | IsBounded (HasOnly:0 b) = contradiction (HasOnly:0-lemma (suc b) xs) ¬max
next-number-is-LUB xs ys ¬max prop | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-is-LUB-Digit+Offset≥2 xs ys ¬max d+o≥2 prop

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
