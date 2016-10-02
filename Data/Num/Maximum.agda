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




digit-1 : ∀ {d o} → d + o > 0 → Digit (suc d)
digit-1 {zero}  {zero}  ()
digit-1 {suc d} {zero}  p = s z
digit-1 {d}     {suc o} p = z

data NextView-0 : ℕ → ℕ → Set where
    HasOnly:0 :                                  NextView-0 0 0
    Others : ∀ {d o} → (bound : d + o ≥ 1 ⊔ o) → NextView-0 d o

nextView-0 : ∀ d o → NextView-0 d o
nextView-0 zero    zero     = HasOnly:0
nextView-0 zero    (suc o)  = Others (s≤s ≤-refl)
nextView-0 (suc d) zero     = Others (s≤s z≤n)
nextView-0 (suc d) (suc o)  = Others (m≤n+m (suc o) (suc d))

-- m ⊓ (n ⊔ o) → m ⊓ n ⊔ m ⊓ o
-- m⊓n≤m
-- m≤m⊔n
next-number-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → ¬ (Maximum xs)
    → Num 0 (suc d) o
next-number-Base≡0 {d} {o} xs ¬max with nextView-0 d o
next-number-Base≡0 xs         ¬max | HasOnly:0    = contradiction (next-number-lemma-6 zero zero xs (s≤s z≤n)) ¬max
next-number-Base≡0 {d} {o} ∙  ¬max | Others bound = Digit-fromℕ {d} {o} (1 ⊔ o) bound ∷ ∙
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

next-number-Digit+Offset≥2-lemma : ∀ m n → 2 ≤ suc m + n → m + n ≥ 1 ⊔ n
next-number-Digit+Offset≥2-lemma m zero    q = ≤-pred q
next-number-Digit+Offset≥2-lemma m (suc n) q = m≤n+m (suc n) m

next-number-Digit+Offset≥2 : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → ¬ (Maximum xs)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → Num (suc b) (suc d) o
next-number-Digit+Offset≥2 {_} {d} {o} ∙        ¬max p = Digit-fromℕ {d} {o} (1 ⊔ o) (next-number-Digit+Offset≥2-lemma d o p) ∷ ∙
-- next-number-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p with toℕ (next-number-Digit+Offset≥2 xs {!next-number-lemma-3 x xs ¬max    !} {!   !}) ∸ toℕ xs
-- ... | q = {!   !}
next-number-Digit+Offset≥2 {_} {d} {o} (x ∷ xs) ¬max p with Greatest? x
next-number-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest with suc b ≤? d
next-number-Digit+Offset≥2 (x ∷ xs) ¬max p | yes greatest | yes redundant
    = digit+1-b x (s≤s redundant) greatest ∷ next-number-Digit+Offset≥2 xs (next-number-lemma-3 x xs ¬max greatest p) p
next-number-Digit+Offset≥2 (x ∷ xs) ¬max p | yes greatest | no ¬redundant
    = z ∷ next-number-Digit+Offset≥2 xs (next-number-lemma-3 x xs ¬max greatest p) p
next-number-Digit+Offset≥2 {_} {d} {o} (x ∷ xs) ¬max p | no ¬greatest = digit+1 x ¬greatest ∷ xs


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
next-number : ∀ {b d o}
    → (xs : Num b d o)
    → ¬ (Maximum xs)
    → Num b d o
next-number {b} {d} {o} xs ¬max with boundedView b d o
next-number xs ¬max | IsBounded (Base≡0 d o) = next-number-Base≡0 xs ¬max
next-number xs ¬max | IsBounded (HasNoDigit b o) = next-number-HasNoDigit xs ¬max
next-number xs ¬max | IsBounded (HasOnly:0 b) = next-number-HasOnly:0 xs ¬max
next-number xs ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-Digit+Offset≥2 xs ¬max d+o≥2




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
    ≤⟨ +n-mono 0 (reflexive (sym (Digit-toℕ-fromℕ {d} (next-number-Digit+Offset≥2-lemma d o p) $
        start
            o
        ≤⟨ m≤m⊔n o (suc zero) ⟩
            o ⊔ suc zero
        ≤⟨ reflexive (⊔-comm o (suc zero)) ⟩
            suc zero ⊔ o
        □)))
    ⟩
        Digit-toℕ (Digit-fromℕ {d} {o} (1 ⊔ o) (next-number-Digit+Offset≥2-lemma d o p)) o + zero
    □
next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p with Greatest? x
next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest with suc b ≤? d
next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest | yes redundant =
    let
        ¬max[xs] = next-number-lemma-3 x xs ¬max greatest p
    in
    start
        suc (Fin.toℕ x + o) + toℕ xs * suc b
    ≤⟨ {! ``  !} ⟩
        {!   !}
    ≤⟨ {!   !} ⟩
        Fin.toℕ x ∸ suc b + o + suc (b + toℕ xs * suc b)
    ≤⟨ +n-mono (suc b + toℕ xs * suc b) (reflexive (sym (Digit-toℕ-digit+1-b {suc b} {suc d} x (s≤s redundant) greatest))) ⟩
        Digit-toℕ {suc d} (digit+1-b {suc b} {suc d} x (s≤s redundant) greatest) o + suc (b + toℕ xs * suc b)
    ≤⟨ n+-mono (Digit-toℕ (digit+1-b {suc b} {suc d} x (s≤s redundant) greatest) o) (*n-mono (suc b) (next-number-is-greater-Digit+Offset≥2 xs ¬max[xs] p)) ⟩
        Digit-toℕ {suc d} (digit+1-b {suc b} {suc d} x (s≤s redundant) greatest) o + toℕ (next-number-Digit+Offset≥2 xs ¬max[xs] p) * suc b
    □
next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | yes greatest | no ¬redundant =
    let
        ¬max[xs] = next-number-lemma-3 x xs ¬max greatest p
    in
    start
        suc (Digit-toℕ x o) + toℕ xs * suc b
    ≤⟨ reflexive (cong (λ w → suc w + toℕ xs * suc b) (toℕ-greatest x greatest)) ⟩
        suc d + o + toℕ xs * suc b
    ≤⟨ reflexive (+-assoc (suc d) o (toℕ xs * suc b)) ⟩
        suc d + (o + toℕ xs * suc b)
    ≤⟨ +n-mono (o + toℕ xs * suc b) (≰⇒> ¬redundant) ⟩
        suc b + (o + toℕ xs * suc b)
    ≤⟨ reflexive (a+[b+c]≡b+[a+c] (suc b) o (toℕ xs * suc b)) ⟩
        o + (suc b + toℕ xs * suc b)
    ≤⟨ n+-mono o (*n-mono (suc b) (next-number-is-greater-Digit+Offset≥2 xs ¬max[xs] p)) ⟩
        o + toℕ (next-number-Digit+Offset≥2 xs ¬max[xs] p) * suc b
    □
next-number-is-greater-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ¬max p | no ¬greatest = {!   !}

-- next-number-Digit+Offset≥2 (x ∷ xs) ¬max p | yes greatest = z ∷ next-number-Digit+Offset≥2 xs (next-number-lemma-3 x xs ¬max greatest p) p
-- next-number-Digit+Offset≥2 (x ∷ xs) ¬max p | no ¬greatest = digit+1 x ¬greatest ∷ xs
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


next-number-is-greater : ∀ {b d o}
    → (xs : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → toℕ (next-number xs ¬max) > toℕ xs
next-number-is-greater {b} {d} {o} xs ¬max with boundedView b d o
next-number-is-greater xs ¬max | IsBounded (Base≡0 d o) = next-number-is-greater-Base≡0 xs ¬max
next-number-is-greater xs ¬max | IsBounded (HasNoDigit b o) = next-number-is-greater-HasNoDigit xs ¬max
next-number-is-greater xs ¬max | IsBounded (HasOnly:0 b) = next-number-is-greater-HasOnly:0 xs ¬max
next-number-is-greater xs ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = {!   !}
-- next-number-is-greater xs ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-is-greater-Digit+Offset≥2 xs ¬max d+o≥2

-- next-number-is-greater : ∀ {b d o}
--     → (xs : Num b d o)
--     → (¬max : ¬ (Maximum xs))
--     → toℕ (next-number xs ¬max) > toℕ xs
-- next-number-is-greater {b} {d} {o} xs ¬max with boundedView b d o
-- next-number-is-greater ∙ ¬max | IsBounded (Base≡0 d o)          with 1 ≤? d + o
-- next-number-is-greater ∙ ¬max | IsBounded (Base≡0 zero zero)    | yes ()
-- next-number-is-greater ∙ ¬max | IsBounded (Base≡0 (suc d) zero) | yes p = s≤s z≤n
-- next-number-is-greater ∙ ¬max | IsBounded (Base≡0 zero (suc o)) | yes p = s≤s z≤n
-- next-number-is-greater ∙ ¬max | IsBounded (Base≡0 (suc d) (suc o)) | yes p = s≤s z≤n
-- next-number-is-greater ∙ ¬max | IsBounded (Base≡0 d o)          | no ¬p = contradiction (next-number-lemma-5 d o (≰⇒> ¬p)) ¬max
-- next-number-is-greater ∙ ¬max | IsBounded (HasNoDigit b o)      = contradiction (HasNoDigit-lemma b o) ¬max
-- next-number-is-greater ∙ ¬max | IsBounded (HasOnly:0 b)         = contradiction (HasOnly:0-lemma (suc b) ∙) ¬max
-- next-number-is-greater ∙ ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = {!   !}
-- next-number-is-greater (x ∷ xs) ¬max | cond with Greatest? x
-- next-number-is-greater (x ∷ xs) ¬max | IsBounded (Base≡0 d o) | yes greatest = contradiction (Base≡0-lemma x xs greatest) ¬max
-- next-number-is-greater (() ∷ xs) ¬max | IsBounded (HasNoDigit b o) | yes greatest
-- next-number-is-greater (x ∷ xs) ¬max | IsBounded (HasOnly:0 b) | yes greatest = contradiction (HasOnly:0-lemma (suc b) (x ∷ xs)) ¬max
-- next-number-is-greater (x ∷ xs) ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) | yes greatest with Greatest? x
-- next-number-is-greater (x ∷ xs) ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) | yes greatest | yes p = {! 0  !}
-- next-number-is-greater (x ∷ xs) ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) | yes greatest | no ¬p = contradiction greatest ¬p
-- next-number-is-greater (x ∷ xs) ¬max | IsBounded (Base≡0 d o) | no ¬greatest = {!    !}
-- next-number-is-greater (x ∷ xs) ¬max | IsBounded (HasNoDigit b o) | no ¬greatest = {!   !}
-- next-number-is-greater (x ∷ xs) ¬max | IsBounded (HasOnly:0 b) | no ¬greatest = {!   !}
-- next-number-is-greater (x ∷ xs) ¬max | IsntBounded cond | no ¬greatest = {!   !}

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



--
-- next-number ∙         ¬max | IsBounded (Base≡0 d o)             with 1 ≤? d + o
-- next-number ∙         ¬max | IsBounded (Base≡0 zero zero)       | yes ()
-- next-number ∙         ¬max | IsBounded (Base≡0 (suc d) zero)    | yes p = s z ∷ ∙
-- next-number ∙         ¬max | IsBounded (Base≡0 zero (suc o))    | yes p = z ∷ ∙
-- next-number ∙         ¬max | IsBounded (Base≡0 (suc d) (suc o)) | yes p = z ∷ ∙
-- next-number ∙         ¬max | IsBounded (Base≡0 d o)             | no ¬p = contradiction (next-number-lemma-5 d o (≰⇒> ¬p)) ¬max
-- next-number ∙         ¬max | IsBounded (HasNoDigit b o)         = contradiction (HasNoDigit-lemma b o) ¬max
-- next-number ∙         ¬max | IsBounded (HasOnly:0 b)            = contradiction (HasOnly:0-lemma (suc b) ∙) ¬max
-- next-number ∙         ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2)
--     = z ∷ ∙
-- next-number (x  ∷ xs) ¬max | cond with Greatest? x
-- next-number (x  ∷ xs) ¬max | IsBounded (Base≡0 d o)     | yes greatest = contradiction (Base≡0-lemma x xs greatest) ¬max -- next-number-lemma-1 {d} {o} x xs ¬max greatest
-- next-number (() ∷ xs) ¬max | IsBounded (HasNoDigit b o) | yes greatest
-- next-number (x  ∷ xs) ¬max | IsBounded (HasOnly:0 b)    | yes greatest = contradiction (HasOnly:0-lemma (suc b) (x ∷ xs)) ¬max
-- next-number (x  ∷ xs) ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) | yes greatest
--     = z ∷ next-number xs (next-number-lemma-3 x xs ¬max greatest d+o≥2)
-- -- next-number (x  ∷ xs) ¬max | cond | no ¬greatest = digit+1 x ¬greatest ∷ xs
-- next-number (x ∷ xs) ¬max | IsBounded (Base≡0 d o) | no ¬greatest = digit+1 x ¬greatest ∷ xs
-- next-number (x ∷ xs) ¬max | IsBounded (HasNoDigit b o) | no ¬greatest = {!   !}
-- next-number (x ∷ xs) ¬max | IsBounded (HasOnly:0 b) | no ¬greatest = {!   !}
-- next-number (x ∷ xs) ¬max | IsntBounded cond | no ¬greatest = {!   !}
