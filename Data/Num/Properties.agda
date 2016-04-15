module Data.Num.Properties where

open import Data.Num

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin.Properties hiding (setoid)
open import Data.Fin as Fin
    using (Fin; #_; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)

open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)
-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
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


WithZero≢Spurious : ∀ {b d} → b ≥ 1 → d ≥ 2 → d ≥ b → notSpurious b d 0
WithZero≢Spurious ()  d≥2      b≤d Base≡0
WithZero≢Spurious b≥1 ()       b≤d NoDigits
WithZero≢Spurious b≥1 d≥2      b≤d (Offset≥2 ())
WithZero≢Spurious b≥1 (s≤s ()) b≤d UnaryWithOnly0s
WithZero≢Spurious b≥1 d≥2      b≤d (NotEnoughDigits _ _ _ p) = contradiction b≤d p

Zeroless≢Spurious : ∀ {b d} → b ≥ 1 → d ≥ 1 → d ≥ b → notSpurious b d 1
Zeroless≢Spurious ()  d≥1 b≤d Base≡0
Zeroless≢Spurious b≥1 ()  b≤d NoDigits
Zeroless≢Spurious b≥1 d≥1 b≤d (Offset≥2 (s≤s ()))
Zeroless≢Spurious b≥1 d≥1 b≤d (NotEnoughDigits _ _ _ p) = contradiction b≤d p

toℕ-digit+1-b : ∀ {d b} (x : Digit d) → (b≥1 : b ≥ 1) → (p : suc (Fin.toℕ x) ≡ d)
    → Fin.toℕ (digit+1-b x b≥1 p) ≡ suc (Fin.toℕ x) ∸ b
toℕ-digit+1-b {d} {b} x b≥1 p = toℕ-fromℕ≤ $ start
        suc (suc (Fin.toℕ x) ∸ b)
    ≤⟨ s≤s (∸-mono ≤-refl b≥1) ⟩
        suc (Fin.toℕ x)
    ≤⟨ reflexive p ⟩
        d
    □

toℕ-1+ : ∀ {b d o}
    → {✓ : notSpurious b d o}
    → (xs : Num b d o)
    → toℕ (1+ xs) ≡ suc (toℕ xs)
toℕ-1+ {b} {d} {o} xs   with surjectionView b d o
toℕ-1+ {b} {d}     ∙    | WithZero b≥1 d≥2 b≤d  =
    begin
        Fin.toℕ (fromℕ≤ d≥2) + b * zero
    ≡⟨ cong (λ x → Fin.toℕ (fromℕ≤ d≥2) + x) (*-right-zero b) ⟩
        Fin.toℕ (fromℕ≤ d≥2) + zero
    ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ d≥2)) ⟩
        Fin.toℕ (fromℕ≤ d≥2)
    ≡⟨ toℕ-fromℕ≤ d≥2 ⟩
        suc zero
    ∎
toℕ-1+ {b} {d} (x ∷ xs) | WithZero b≥1 d≥2 b≤d with full x
toℕ-1+ {b} {d} (x ∷ xs) | WithZero b≥1 d≥2 b≤d | yes p =
    begin
        Fin.toℕ {d} (digit+1-b x b≥1 p) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ (digit+1-b-lemma x b≥1 p)) ⟩    -- toℕ-fromℕ≤
        suc (Fin.toℕ x) ∸ b + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ b + b * w) (toℕ-1+ {✓ = WithZero≢Spurious b≥1 d≥2 b≤d} xs) ⟩        -- induction
        suc (Fin.toℕ x) ∸ b + b * suc (toℕ xs)
    ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ b + w) (*-comm b (suc (toℕ xs))) ⟩
        suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b)
    ≡⟨ sym (+-assoc (suc (Fin.toℕ x) ∸ b) b (toℕ xs * b)) ⟩
        suc (Fin.toℕ x) ∸ b + b + toℕ xs * b
    ≡⟨ cong (λ w → w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
        b + (suc (Fin.toℕ x) ∸ b) + toℕ xs * b
    ≡⟨ cong (λ w → w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
            start
                b
            ≤⟨ b≤d ⟩
                d
            ≤⟨ reflexive (sym p) ⟩
                suc (Fin.toℕ x)
            □)) ⟩
        suc (Fin.toℕ x) + toℕ xs * b
    ≡⟨ cong (λ w → suc (Fin.toℕ x) + w) (*-comm (toℕ xs) b) ⟩
        suc (Fin.toℕ x + b * toℕ xs)
    ∎
toℕ-1+ {b} {d} (x ∷ xs) | WithZero b≥1 d≥2 b≤d | no ¬p =
    cong (λ w → w + b * toℕ xs) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p))
toℕ-1+ {b} {d} ∙        | Zeroless b≥1 d≥1 b≤d =
    begin
        suc (Fin.toℕ (fromℕ≤ d≥1) + b * zero)
    ≡⟨ cong (λ x → suc (Fin.toℕ (fromℕ≤ d≥1)) + x) (*-right-zero b) ⟩
        suc (Fin.toℕ (fromℕ≤ d≥1) + zero)
    ≡⟨ cong (λ x → suc x + 0) (toℕ-fromℕ≤ d≥1) ⟩
        suc zero
    ∎
toℕ-1+ {b} {d} (x ∷ xs) | Zeroless b≥1 d≥1 b≤d with full x
toℕ-1+ {b} {d} (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | yes p =
    begin
        suc (Fin.toℕ (digit+1-b x b≥1 p)) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → suc w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ (digit+1-b-lemma x b≥1 p)) ⟩    -- toℕ-fromℕ≤
        suc (suc (Fin.toℕ x) ∸ b) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → suc (suc (Fin.toℕ x) ∸ b) + b * w) (toℕ-1+ {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d} xs) ⟩      -- induction
        suc (suc (Fin.toℕ x) ∸ b + b * suc (toℕ xs))
    ≡⟨ cong (λ w → suc (suc (Fin.toℕ x) ∸ b + w)) (*-comm b (suc (toℕ xs))) ⟩
        suc (suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b))
    ≡⟨  sym (+-assoc (suc (suc (Fin.toℕ x) ∸ b)) b (toℕ xs * b)) ⟩
        suc (suc (Fin.toℕ x) ∸ b + b + toℕ xs * b)
    ≡⟨ cong (λ w → suc w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
        suc (b + (suc (Fin.toℕ x) ∸ b)) + toℕ xs * b
    ≡⟨ cong (λ w → suc w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
            start
                b
            ≤⟨ b≤d ⟩
                d
            ≤⟨ reflexive (sym p) ⟩
                suc (Fin.toℕ x)
            □)) ⟩
        suc (suc (Fin.toℕ x + toℕ xs * b))
    ≡⟨ cong (λ w → suc (suc (Fin.toℕ x + w))) (*-comm (toℕ xs) b) ⟩
        suc (suc (Fin.toℕ x + b * toℕ xs))
    ∎
toℕ-1+ {b} {d} (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | no ¬p =
    cong (λ w → suc w + b * toℕ xs) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p))
toℕ-1+ {✓ = claim} xs      | Spurious reason = contradiction refl (claim reason)


1+-fromℕ : ∀ {b d o}
    → {✓ : notSpurious b d o}
    → (n : ℕ)
    → 1+ (fromℕ {b} {d} {o} n) ≡ fromℕ (suc n)
1+-fromℕ {b} {d} {o} n with surjectionView b d o | inspect (surjectionView b d) o
1+-fromℕ             n | WithZero b≥1 d≥2 b≤d | [ eq ] rewrite eq = refl
1+-fromℕ             n | Zeroless b≥1 d≥1 b≤d | [ eq ] rewrite eq = refl
1+-fromℕ {✓ = claim} n | Spurious reason      | [ eq ] = contradiction refl (claim reason)

toℕ-fromℕ : ∀ {b d o}
    → {✓ : notSpurious b d o}
    → (n : ℕ)
    → toℕ (fromℕ {b} {d} {o} n) ≡ n
toℕ-fromℕ {b} {d} {o} n       with surjectionView b d o
toℕ-fromℕ {b} {d}     zero    | WithZero b≥1 d≥2 b≤d = refl
toℕ-fromℕ {b} {d}     (suc n) | WithZero b≥1 d≥2 b≤d =
    begin
        toℕ (1+ (fromℕ {b} {d} n))
    ≡⟨ toℕ-1+ {✓ = WithZero≢Spurious b≥1 d≥2 b≤d} (fromℕ {b} {d} n) ⟩
        suc (toℕ (fromℕ {b} {d} n))
    ≡⟨ cong suc (toℕ-fromℕ {b} {d} {✓ = WithZero≢Spurious b≥1 d≥2 b≤d} n) ⟩
        suc n
    ∎
toℕ-fromℕ {b} {d}     zero    | Zeroless b≥1 d≥1 b≤d = refl
toℕ-fromℕ {b} {d}     (suc n) | Zeroless b≥1 d≥1 b≤d =
    begin
        toℕ (1+ (fromℕ {b} {d} n))
    ≡⟨ toℕ-1+ {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d} (fromℕ {b} {d} n) ⟩
        suc (toℕ (fromℕ {b} {d} n))
    ≡⟨ cong suc (toℕ-fromℕ {b} {d} {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d} n) ⟩
        suc n
    ∎
toℕ-fromℕ {✓ = claim}   n     | Spurious reason = contradiction refl (claim reason)


open import Function.Equality hiding (setoid; cong; _∘_; id)
open import Function.Surjection hiding (id; _∘_)
open Surjective

-- fromℕ that preserves equality
ℕ⟶Num : ∀ b d o → setoid ℕ ⟶ Num-Setoid b d o
ℕ⟶Num b d o = record
    { _⟨$⟩_ = fromℕ
    ; cong = cong (toℕ ∘ fromℕ {b} {d} {o})
    }

-- toℕ that preserves equality
Num⟶ℕ : ∀ b d o → Num-Setoid b d o ⟶ setoid ℕ
Num⟶ℕ b d o = record { _⟨$⟩_ = toℕ ; cong = id }

lemma1 : ∀ {d o} → (xs : Num 0 d o) → toℕ xs ≤ o + d
lemma1 {d} {o} ∙        = z≤n
lemma1 {d} {o} (x ∷ xs) =
    start
        o + Fin.toℕ x + zero
    ≤⟨ reflexive (+-right-identity (o + Fin.toℕ x)) ⟩
        o + Fin.toℕ x
    ≤⟨ _+-mono_ {o} {o} {Fin.toℕ x} {d} ≤-refl (
        start
            Fin.toℕ x
        ≤⟨ n≤1+n (Fin.toℕ x) ⟩
            suc (Fin.toℕ x)
        ≤⟨ bounded x ⟩
            d
        □
    ) ⟩
        o + d
    □

lemma2 : ∀ {b o} → (xs : Num b 0 o) → toℕ xs ≢ 1
lemma2 ∙ = λ ()
lemma2 (() ∷ xs)

lemma3 : ∀ {b d o} → (xs : Num b d o) → o ≥ 2 → toℕ xs ≢ 1
lemma3 ∙        o≥2 = λ ()
lemma3 {o = zero} (x ∷ xs) () p
lemma3 {o = suc zero} (x ∷ xs) (s≤s ()) p
lemma3 {o = suc (suc o)} (x ∷ xs) o≥2 ()

lemma4 : (xs : Num 1 1 0) → toℕ xs ≢ 1
lemma4 ∙ ()
lemma4 (z ∷ xs) p = contradiction (begin
        toℕ xs
    ≡⟨ sym (+-right-identity (toℕ xs)) ⟩
        toℕ xs + zero
    ≡⟨ p ⟩
        suc zero
    ∎) (lemma4 xs)
lemma4 (s () ∷ xs)

lemma5-0 : ∀ {b d} → (xs : Num b d 0) → b ≥ 1 → d ≥ 1 → b ≰ d → toℕ xs ≢ d
lemma5-0 ∙        b≥1 () b≰d refl
lemma5-0 (x ∷ xs) b≥1 d≥1 b≰d p with toℕ xs ≤? 0
lemma5-0 {b} {d} (x ∷ xs) b≥1 d≥1 b≰d p | yes q =
    contradiction p (<⇒≢ ⟦x∷xs⟧>d)
    where
        ⟦xs⟧≡0 : toℕ xs ≡ 0
        ⟦xs⟧≡0 = ≤0⇒≡0 (toℕ xs) q
        ⟦x∷xs⟧>d : Fin.toℕ x + b * toℕ xs < d
        ⟦x∷xs⟧>d =
            start
                suc (Fin.toℕ x + b * toℕ xs)
            ≤⟨ reflexive (cong (λ w → suc (Fin.toℕ x + b * w)) ⟦xs⟧≡0) ⟩
                suc (Fin.toℕ x + b * zero)
            ≤⟨ reflexive (cong (λ w → suc (Fin.toℕ x + w)) (*-right-zero b)) ⟩
                suc (Fin.toℕ x + zero)
            ≤⟨ reflexive (+-right-identity (suc (Fin.toℕ x))) ⟩
                suc (Fin.toℕ x)
            ≤⟨ bounded x ⟩
                d
            □
lemma5-0 {b} {d} (x ∷ xs) b≥1 d≥1 b≰d p | no ¬q =
    contradiction p (>⇒≢ ⟦x∷xs⟧>d)
    where
        ⟦x∷xs⟧>d : Fin.toℕ x + b * toℕ xs > d
        ⟦x∷xs⟧>d =
            start
                suc d
            ≤⟨ ≰⇒> b≰d ⟩
                b
            ≤⟨ reflexive (sym (*-right-identity b)) ⟩
                b * 1
            ≤⟨ _*-mono_ {b} {b} {1} {toℕ xs} ≤-refl (≰⇒> ¬q) ⟩
                b * toℕ xs
            ≤⟨ n≤m+n (Fin.toℕ x) (b * toℕ xs) ⟩
                Fin.toℕ x + b * toℕ xs
            □

lemma5-1 : ∀ {b d} → (xs : Num b d 1) → b ≰ d → toℕ xs ≢ suc d
lemma5-1 ∙        b≰d = (λ ())
lemma5-1 (x ∷ xs) b≰d p with toℕ xs ≤? 0
lemma5-1 {b} {d} (x ∷ xs) b≰d p | yes q =
    contradiction p (<⇒≢ (s≤s ⟦x∷xs⟧>d))
    where
        ⟦xs⟧≡0 : toℕ xs ≡ 0
        ⟦xs⟧≡0 = ≤0⇒≡0 (toℕ xs) q
        ⟦x∷xs⟧>d : Fin.toℕ x + b * toℕ xs < d
        ⟦x∷xs⟧>d =
            start
                suc (Fin.toℕ x + b * toℕ xs)
            ≤⟨ reflexive (cong (λ w → suc (Fin.toℕ x + b * w)) ⟦xs⟧≡0) ⟩
                suc (Fin.toℕ x + b * zero)
            ≤⟨ reflexive (cong (λ w → suc (Fin.toℕ x + w)) (*-right-zero b)) ⟩
                suc (Fin.toℕ x + zero)
            ≤⟨ reflexive (+-right-identity (suc (Fin.toℕ x))) ⟩
                suc (Fin.toℕ x)
            ≤⟨ bounded x ⟩
                d
            □
lemma5-1 {b} {d} (x ∷ xs) b≰d p | no ¬q =
    contradiction p (>⇒≢ (s≤s ⟦x∷xs⟧>d))
    where
        ⟦x∷xs⟧>d : Fin.toℕ x + b * toℕ xs > d
        ⟦x∷xs⟧>d =
            start
                suc d
            ≤⟨ ≰⇒> b≰d ⟩
                b
            ≤⟨ reflexive (sym (*-right-identity b)) ⟩
                b * 1
            ≤⟨ _*-mono_ {b} {b} {1} {toℕ xs} ≤-refl (≰⇒> ¬q) ⟩
                b * toℕ xs
            ≤⟨ n≤m+n (Fin.toℕ x) (b * toℕ xs) ⟩
                Fin.toℕ x + b * toℕ xs
            □

Spurious⇏Surjective : ∀ {b} {d} {o} → WhySpurious b d o → ¬ (Surjective (Num⟶ℕ b d o))
Spurious⇏Surjective {_} {d} {o} Base≡0              claim =
    contradiction ≡1+o+d (<⇒≢ <1+o+d)
    where
        ≡1+o+d : toℕ (from claim ⟨$⟩ suc (o + d)) ≡ suc (o + d)
        ≡1+o+d = right-inverse-of claim (suc o + d)
        <1+o+d : toℕ (from claim ⟨$⟩ suc (o + d)) < suc (o + d)
        <1+o+d = s≤s (lemma1 (from claim ⟨$⟩ suc o + d))
Spurious⇏Surjective NoDigits            claim =
    contradiction (right-inverse-of claim 1) (lemma2 (from claim ⟨$⟩ 1))
Spurious⇏Surjective (Offset≥2 p)        claim =
    contradiction (right-inverse-of claim 1) (lemma3 (_⟨$⟩_ (from claim) 1) p)
Spurious⇏Surjective UnaryWithOnly0s     claim =
    contradiction (right-inverse-of claim 1) (lemma4 (_⟨$⟩_ (from claim) 1))
Spurious⇏Surjective {_} {d} {0} (NotEnoughDigits p q r t) claim = lemma5-0 (_⟨$⟩_ (from claim) d) p q t (right-inverse-of claim d)
Spurious⇏Surjective {_} {d} {1} (NotEnoughDigits p q r t) claim = lemma5-1 (_⟨$⟩_ (from claim) (suc d)) t (right-inverse-of claim (suc d))
Spurious⇏Surjective {_} {_} {suc (suc o)} (NotEnoughDigits b≥1 d≥1 (s≤s (s≤s ())) b≰d) claim

Surjective? : ∀ b d o → Dec (Surjective (Num⟶ℕ b d o))
Surjective? b d o with surjectionView b d o
Surjective? b d 0 | WithZero b≥1 d≥2 b≤d = yes (record
    { from = ℕ⟶Num b d 0
    ; right-inverse-of = toℕ-fromℕ {b} {d} {✓ = WithZero≢Spurious b≥1 d≥2 b≤d}
    })
Surjective? b d 1 | Zeroless b≥1 d≥1 b≤d = yes (record
    { from = ℕ⟶Num b d 1
    ; right-inverse-of = toℕ-fromℕ {b} {d} {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d}
    })
Surjective? b d _ | Spurious reason = no (Spurious⇏Surjective reason)

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
