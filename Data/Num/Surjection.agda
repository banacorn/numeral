module Data.Num.Surjection where

open import Data.Num.Core

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra

open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)

open import Function
open import Function.Surjection hiding (_∘_)
open Surjective
open import Function.Equality using (_⟶_; _⟨$⟩_)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

data WhySpurious : ℕ → ℕ → ℕ → Set where
    Base≡0          : ∀ {  d o}          → WhySpurious 0 d o
    NoDigits        : ∀ {b   o}          → WhySpurious b 0 o
    Offset≥2        : ∀ {b d o} → o ≥ 2 → WhySpurious b d o
    UnaryWithOnly0s :                      WhySpurious 1 1 0
    NotEnoughDigits : ∀ {b d o} → d ≥ 1 → b ≰ d → WhySpurious b d o

data SurjectionView : ℕ → ℕ → ℕ → Set where
    WithZero : ∀ {b d} → (b≥1 : b ≥ 1) → (d≥2 : d ≥ 2) → (b≤d : b ≤ d) → SurjectionView b d 0
    Zeroless : ∀ {b d} → (b≥1 : b ≥ 1) → (d≥1 : d ≥ 1) → (b≤d : b ≤ d) → SurjectionView b d 1
    Spurious : ∀ {b d o} → WhySpurious b d o → SurjectionView b d o

surjectionView : (b d o : ℕ) → SurjectionView b d o
-- # base = 0
surjectionView 0             d             o = Spurious Base≡0
-- # base ≥ 1
surjectionView (suc b)       0             o = Spurious NoDigits
--      # starts from 0 (offset = 0)
surjectionView (suc b)       (suc d)       0 with suc b ≤? suc d
surjectionView 1             1             0 | yes p = Spurious UnaryWithOnly0s
surjectionView (suc (suc b)) 1             0 | yes (s≤s ())
surjectionView 1             (suc (suc d)) 0 | yes p = WithZero (s≤s z≤n) (s≤s (s≤s z≤n)) p
surjectionView (suc (suc b)) (suc (suc d)) 0 | yes p = WithZero (s≤s z≤n) (≤-trans (s≤s (s≤s z≤n)) p) p
    where   open import Data.Nat.Properties.Extra using (≤-trans)
surjectionView (suc b)       (suc d)       0 | no ¬p = Spurious (NotEnoughDigits (s≤s z≤n) ¬p)        -- not enough digits
--      # starts from 1 (offset = 1)
surjectionView (suc b)       (suc d)       1 with suc b ≤? suc d
surjectionView (suc b)       (suc d)       1 | yes p = Zeroless (s≤s z≤n) (s≤s z≤n) p
surjectionView (suc b)       (suc d)       1 | no ¬p = Spurious (NotEnoughDigits (s≤s z≤n) ¬p)        -- not enough digits

surjectionView (suc b)       (suc d)       (suc (suc o)) = Spurious (Offset≥2 (s≤s (s≤s z≤n)))    -- offset ≥ 2

notSpurious : ℕ → ℕ → ℕ → Set
notSpurious b d o = ∀ reason → surjectionView b d o ≢ Spurious reason

------------------------------------------------------------------------
-- Surjective operations on Num
------------------------------------------------------------------------


digit+1-b-lemma : ∀ {b d} → (x : Digit d)
    → b ≥ 1 → suc (Fin.toℕ x) ≡ d
    → suc (Fin.toℕ x) ∸ b < d
digit+1-b-lemma {b} {d} x b≥1 p =
    start
        suc (suc (Fin.toℕ x) ∸ b)
    ≤⟨ s≤s (∸-mono ≤-refl b≥1) ⟩
        suc (Fin.toℕ x)
    ≤⟨ reflexive p ⟩
        d
    □

digit+1-b : ∀ {b d} → (x : Digit d) → b ≥ 1 → suc (Fin.toℕ x) ≡ d → Fin d
digit+1-b {b} {d} x b≥1 p = fromℕ≤ {suc (Fin.toℕ x) ∸ b} (digit+1-b-lemma x b≥1 p)

digit+1 : ∀ {d} → (x : Digit d) → (¬p : suc (Fin.toℕ x) ≢ d) → Fin d
digit+1 x ¬p = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p)

1+ : ∀ {b d o}
    → Num b d o
    → Num b d o
1+ {b} {d} {o} xs with surjectionView b d o
1+ ∙        | WithZero b≥1 d≥2 b≤d = fromℕ≤ {1} d≥2 ∷ ∙                -- e.g.   ⇒ 1
1+ (x ∷ xs) | WithZero b≥1 d≥2 b≤d with full x
1+ (x ∷ xs) | WithZero b≥1 d≥2 b≤d | yes p = digit+1-b x b≥1 p ∷ 1+ xs  --      n ⇒ n + 1 - base
1+ (x ∷ xs) | WithZero b≥1 d≥2 b≤d | no ¬p = digit+1   x    ¬p ∷ xs     --      n ⇒ n + 1
1+ ∙        | Zeroless b≥1 d≥1 b≤d = fromℕ≤ {0} d≥1 ∷ ∙                -- e.g. 9 ⇒ 10
1+ (x ∷ xs) | Zeroless b≥1 d≥1 b≤d with full x
1+ (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | yes p = digit+1-b x b≥1 p ∷ 1+ xs  --      n ⇒ n + 1 - base
1+ (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | no ¬p = digit+1   x    ¬p ∷ xs     --      n ⇒ n + 1
1+ xs       | Spurious _ = xs


fromℕ : ∀ {b d o} → ℕ → Num b d o
fromℕ {b} {d} {o} n with surjectionView b d o
fromℕ zero    | WithZero b≥1 d≥2 b≤d = ∙
fromℕ (suc n) | WithZero b≥1 d≥2 b≤d = 1+ (fromℕ n)
fromℕ zero    | Zeroless b≥1 d≥1 b≤d = ∙
fromℕ (suc n) | Zeroless b≥1 d≥1 b≤d = 1+ (fromℕ n)
fromℕ n       | Spurious _ = ∙


-- fromℕ that preserves equality
ℕ⟶Num : ∀ b d o → setoid ℕ ⟶ Num-Setoid b d o
ℕ⟶Num b d o = record
    { _⟨$⟩_ = fromℕ
    ; cong = cong (toℕ ∘ fromℕ {b} {d} {o})
    }

WithZero≢Spurious : ∀ {b d} → b ≥ 1 → d ≥ 2 → d ≥ b → notSpurious b d 0
WithZero≢Spurious ()  d≥2      b≤d Base≡0
WithZero≢Spurious b≥1 ()       b≤d NoDigits
WithZero≢Spurious b≥1 d≥2      b≤d (Offset≥2 ())
WithZero≢Spurious b≥1 (s≤s ()) b≤d UnaryWithOnly0s
WithZero≢Spurious b≥1 d≥2      b≤d (NotEnoughDigits _ p) = contradiction b≤d p

Zeroless≢Spurious : ∀ {b d} → b ≥ 1 → d ≥ 1 → d ≥ b → notSpurious b d 1
Zeroless≢Spurious ()  d≥1 b≤d Base≡0
Zeroless≢Spurious b≥1 ()  b≤d NoDigits
Zeroless≢Spurious b≥1 d≥1 b≤d (Offset≥2 (s≤s ()))
Zeroless≢Spurious b≥1 d≥1 b≤d (NotEnoughDigits _ p) = contradiction b≤d p

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



------------------------------------------------------------------------
-- Lemmata for proving Spurious cases not surjective
------------------------------------------------------------------------

lemma1 : ∀ {d o} → (xs : Num 0 d o) → toℕ xs ≢ suc (o + d)
lemma1 {d} {o} ∙        ()
lemma1 {d} {o} (x ∷ xs) p =
    contradiction p (<⇒≢ ⟦x∷xs⟧<1+o+d)
    where
        ⟦x∷xs⟧<1+o+d : o + Fin.toℕ x + 0 < suc (o + d)
        ⟦x∷xs⟧<1+o+d = s≤s $
            start
                o + Fin.toℕ x + zero
            ≤⟨ reflexive (+-right-identity (o + Fin.toℕ x)) ⟩
                o + Fin.toℕ x
            ≤⟨ ≤-sucs o (
                start
                    Fin.toℕ x
                ≤⟨ n≤1+n (Fin.toℕ x) ⟩
                    suc (Fin.toℕ x)
                ≤⟨ bounded x ⟩
                    d
                □
            )⟩
                o + d
            □

lemma2 : ∀ {b o} → (xs : Num b 0 o) → toℕ xs ≢ 1
lemma2 ∙         ()
lemma2 (() ∷ xs)

lemma3 : ∀ {b d o} → o ≥ 2 → (xs : Num b d o) → toℕ xs ≢ 1
lemma3                   o≥2      ∙        ()
lemma3 {o = 0}           ()       (x ∷ xs) p
lemma3 {o = 1}           (s≤s ()) (x ∷ xs) p
lemma3 {o = suc (suc o)} o≥2      (x ∷ xs) ()

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

lemma5 : ∀ {b d o} → d ≥ 1 → b ≰ d → (xs : Num b d o) → toℕ xs ≢ o + d
lemma5 {_} {_} {o} d≥1 b≰d ∙        = <⇒≢ (≤-steps o d≥1)
lemma5 {b} {d} {o} d≥1 b≰d (x ∷ xs) p with toℕ xs ≤? 0
lemma5 {b} {d} {o} d≥1 b≰d (x ∷ xs) p | yes q =
    contradiction p (<⇒≢ ⟦x∷xs⟧>o+d)
    where
        ⟦xs⟧≡0 : toℕ xs ≡ 0
        ⟦xs⟧≡0 = ≤0⇒≡0 (toℕ xs) q
        ⟦x∷xs⟧>o+d : o + Fin.toℕ x + b * toℕ xs < o + d
        ⟦x∷xs⟧>o+d = start
                suc (o + Fin.toℕ x + b * toℕ xs)
            ≤⟨ reflexive (begin
                    suc (o + Fin.toℕ x + b * toℕ xs)
                ≡⟨ cong (λ w → suc (o + Fin.toℕ x + b * w)) ⟦xs⟧≡0 ⟩
                    suc (o + Fin.toℕ x + b * zero)
                ≡⟨ cong (λ w → suc (o + Fin.toℕ x + w)) (*-right-zero b) ⟩
                    suc (o + Fin.toℕ x + zero)
                ≡⟨ +-right-identity (suc (o + Fin.toℕ x)) ⟩
                    suc (o + Fin.toℕ x)
                ≡⟨ sym (+-suc o (Fin.toℕ x)) ⟩
                    o + suc (Fin.toℕ x)
                ∎) ⟩
                o + suc (Fin.toℕ x)
            ≤⟨ ≤-sucs o (bounded x) ⟩
                o + d
            □

lemma5 {b} {d} {o} d≥1 b≰d (x ∷ xs) p | no ¬q =
    contradiction p (>⇒≢ ⟦x∷xs⟧>o+d)
    where
        ⟦x∷xs⟧>o+d : o + Fin.toℕ x + b * toℕ xs > o + d
        ⟦x∷xs⟧>o+d = start
                suc (o + d)
            ≤⟨ reflexive (sym (+-suc o d)) ⟩
                o + suc d
            ≤⟨ ≤-sucs o (
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
            ) ⟩
                o + (Fin.toℕ x + b * toℕ xs)
            ≤⟨ reflexive (sym (+-assoc o (Fin.toℕ x) (b * toℕ xs))) ⟩
                o + Fin.toℕ x + b * toℕ xs
            □

Spurious⇏Surjective : ∀ {b} {d} {o} → WhySpurious b d o → ¬ (Surjective (Num⟶ℕ b d o))
Spurious⇏Surjective {_} {d} {o} Base≡0              claim =
    lemma1 (from claim ⟨$⟩ suc o + d) (right-inverse-of claim (suc (o + d)))
Spurious⇏Surjective NoDigits            claim =
    lemma2      (from claim ⟨$⟩ 1)    (right-inverse-of claim 1)
Spurious⇏Surjective (Offset≥2 p)        claim =
    lemma3 p    (from claim ⟨$⟩ 1)    (right-inverse-of claim 1)
Spurious⇏Surjective UnaryWithOnly0s     claim =
    lemma4     (from claim ⟨$⟩ 1)     (right-inverse-of claim 1)
Spurious⇏Surjective {_} {d} {o} (NotEnoughDigits p q) claim =
    lemma5 p q (from claim ⟨$⟩ o + d) (right-inverse-of claim (o + d))

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
