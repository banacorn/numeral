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
open import Data.Product

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

-- Conditions of surjectiveness
data SurjCond : ℕ → ℕ → ℕ → Set where
    WithZerosUnary : ∀ {  d}               → (d≥2 : d ≥ 2) → SurjCond 1 d 0
    WithZeros      : ∀ {b d} (b≥2 : b ≥ 2) → (d≥b : d ≥ b) → SurjCond b d 0
    Zeroless       : ∀ {b d} (b≥1 : b ≥ 1) → (d≥b : d ≥ b) → SurjCond b d 1

-- Conditions of non-surjectiveness
data NonSurjCond : ℕ → ℕ → ℕ → Set where
    Base≡0             : ∀ {  d o}                 → NonSurjCond 0 d o
    NoDigits           : ∀ {b   o}                 → NonSurjCond b 0 o
    Offset≥2           : ∀ {b d o} → o ≥ 2         → NonSurjCond b d o
    UnaryWithOnlyZeros :                              NonSurjCond 1 1 0
    NotEnoughDigits    : ∀ {b d o} → d ≥ 1 → d ≱ b → NonSurjCond b d o

data SurjectionView : ℕ → ℕ → ℕ → Set where
    Surj    : ∀ {b d o} →    SurjCond b d o → SurjectionView b d o
    NonSurj : ∀ {b d o} → NonSurjCond b d o → SurjectionView b d o


surjectionView : (b d o : ℕ) → SurjectionView b d o
surjectionView 0             d             o             = NonSurj Base≡0
surjectionView (suc b)       0             o             = NonSurj NoDigits
surjectionView (suc b)       (suc d)       o             with suc b ≤? suc d
surjectionView 1             1             0             | yes p = NonSurj UnaryWithOnlyZeros
surjectionView 1             (suc (suc d)) 0             | yes p = Surj    (WithZerosUnary (s≤s (s≤s z≤n)))
surjectionView (suc (suc b)) (suc d)       0             | yes p = Surj    (WithZeros (s≤s (s≤s z≤n)) p)
surjectionView (suc b)       (suc d)       1             | yes p = Surj    (Zeroless (s≤s z≤n) p)
surjectionView (suc b)       (suc d)       (suc (suc o)) | yes p = NonSurj (Offset≥2 (s≤s (s≤s z≤n)))
surjectionView (suc b)       (suc d)       o             | no ¬p = NonSurj (NotEnoughDigits (s≤s z≤n) ¬p)

BeSurj : ℕ → ℕ → ℕ → Set
BeSurj b d o = Σ[ condition ∈ SurjCond b d o ] surjectionView b d o ≡ Surj condition

SurjCond⇒b≥1 : ∀ {b d o} → SurjCond b d o → b ≥ 1
SurjCond⇒b≥1 (WithZerosUnary d≥2)      = s≤s z≤n
SurjCond⇒b≥1 (WithZeros (s≤s b≥1) d≥b) = s≤s z≤n
SurjCond⇒b≥1 (Zeroless b≥1 d≥b)        = b≥1

SurjCond⇒d≥b : ∀ {b d o} → SurjCond b d o → d ≥ b
SurjCond⇒d≥b (WithZerosUnary (s≤s d≥1)) = s≤s z≤n
SurjCond⇒d≥b (WithZeros b≥2 d≥b)        = d≥b
SurjCond⇒d≥b (Zeroless b≥1 d≥b)         = d≥b

SurjCond⇒BeSurj : ∀ {b d o} → SurjCond b d o → BeSurj b d o
SurjCond⇒BeSurj {b} {d} {o} condition with surjectionView b d o
SurjCond⇒BeSurj _                         | Surj condition = condition , refl
SurjCond⇒BeSurj (WithZeros () d≥b)        | NonSurj Base≡0
SurjCond⇒BeSurj (Zeroless () d≥b)         | NonSurj Base≡0
SurjCond⇒BeSurj (WithZerosUnary ())       | NonSurj NoDigits
SurjCond⇒BeSurj (WithZeros () z≤n)        | NonSurj NoDigits
SurjCond⇒BeSurj (Zeroless () z≤n)         | NonSurj NoDigits
SurjCond⇒BeSurj (WithZerosUnary _)        | NonSurj (Offset≥2 ())
SurjCond⇒BeSurj (WithZeros _ _)           | NonSurj (Offset≥2 ())
SurjCond⇒BeSurj (Zeroless _ _)            | NonSurj (Offset≥2 (s≤s ()))
SurjCond⇒BeSurj (WithZerosUnary (s≤s ())) | NonSurj UnaryWithOnlyZeros
SurjCond⇒BeSurj (WithZeros (s≤s ()) _)    | NonSurj UnaryWithOnlyZeros
SurjCond⇒BeSurj (WithZerosUnary _)        | NonSurj (NotEnoughDigits d≥1 d≱1) = contradiction d≥1 d≱1
SurjCond⇒BeSurj (WithZeros _ d≥b)         | NonSurj (NotEnoughDigits _ d≱b) = contradiction d≥b d≱b
SurjCond⇒BeSurj (Zeroless _ d≥b)          | NonSurj (NotEnoughDigits _ d≱b) = contradiction d≥b d≱b


------------------------------------------------------------------------
-- Operations on Num (which does not necessary needs to be Surj)
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

1+ : ∀ {b d o} → Num b d o → Num b d o
1+ {b} {d} {o} xs with surjectionView b d o
1+ ∙        | Surj (WithZerosUnary d≥2) = fromℕ≤ {1} d≥2                ∷ ∙  -- starts from 0
1+ ∙        | Surj (WithZeros b≥2 d≥b)  = fromℕ≤ {1} (≤-trans b≥2 d≥b) ∷ ∙  -- starts from 0
1+ ∙        | Surj (Zeroless b≥1 d≥b)   = fromℕ≤ {0} (≤-trans b≥1 d≥b) ∷ ∙  -- starts from 1
1+ (x ∷ xs) | Surj (WithZerosUnary d≥2) with full x
1+ (x ∷ xs) | Surj (WithZerosUnary d≥2) | yes p = digit+1-b x (SurjCond⇒b≥1 (WithZerosUnary d≥2)) p ∷ 1+ xs
1+ (x ∷ xs) | Surj (WithZerosUnary d≥2) | no ¬p = digit+1 x ¬p ∷ xs
1+ (x ∷ xs) | Surj (WithZeros b≥2 d≥b) with full x
1+ (x ∷ xs) | Surj (WithZeros b≥2 d≥b) | yes p = digit+1-b x (SurjCond⇒b≥1 (WithZeros b≥2 d≥b)) p ∷ 1+ xs
1+ (x ∷ xs) | Surj (WithZeros b≥2 d≥b) | no ¬p = digit+1 x ¬p ∷ xs
1+ (x ∷ xs) | Surj (Zeroless b≥1 d≥b) with full x
1+ (x ∷ xs) | Surj (Zeroless b≥1 d≥b) | yes p = digit+1-b x (SurjCond⇒b≥1 (Zeroless b≥1 d≥b)) p ∷ 1+ xs
1+ (x ∷ xs) | Surj (Zeroless b≥1 d≥b) | no ¬p = digit+1 x ¬p ∷ xs
-- 1+ (x ∷ xs) | Surj cond with full x
-- 1+ (x ∷ xs) | Surj cond | yes p = digit+1-b x (SurjCond⇒b≥1 cond) p ∷ 1+ xs -- carry
-- 1+ (x ∷ xs) | Surj cond | no ¬p = digit+1   x ¬p                     ∷    xs
1+ ∙ | NonSurj reason = ∙
1+ (x ∷ xs) | NonSurj reason = xs


n+ : ∀ {b d o} → ℕ → Num b d o → Num b d o
n+ {b} {d} {o} n xs with surjectionView b d o
n+ zero    xs |    Surj cond = xs
n+ (suc n) xs |    Surj cond = 1+ (n+ n xs)
n+ n       xs | NonSurj cond = xs

fromℕ : ∀ {b d o} → ℕ → Num b d o
fromℕ {b} {d} {o} n with surjectionView b d o
fromℕ n |    Surj x = n+ n ∙
fromℕ n | NonSurj x = ∙


-- fromℕ that preserves equality
ℕ⟶Num : ∀ b d o → setoid ℕ ⟶ Num-Setoid b d o
ℕ⟶Num b d o = record
    { _⟨$⟩_ = fromℕ
    ; cong = cong (toℕ ∘ fromℕ {b} {d} {o})
    }

toℕ-digit+1-b : ∀ {d b} (x : Digit d)
    → (b≥1 : b ≥ 1) → (p : suc (Fin.toℕ x) ≡ d)     -- required props
    → Fin.toℕ (digit+1-b x b≥1 p) ≡ suc (Fin.toℕ x) ∸ b
toℕ-digit+1-b {d} {b} x b≥1 p = toℕ-fromℕ≤ $ start
        suc (suc (Fin.toℕ x) ∸ b)
    ≤⟨ s≤s (∸-mono ≤-refl b≥1) ⟩
        suc (Fin.toℕ x)
    ≤⟨ reflexive p ⟩
        d
    □


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

toℕ-1+ : ∀ {b d o}
    → {beSurj : BeSurj b d o}
    → (xs : Num b d o)
    → toℕ (1+ xs) ≡ suc (toℕ xs)
toℕ-1+ {b} {d} {o} xs with surjectionView b d o | inspect (surjectionView b d) o
toℕ-1+ {_} {d} {_} ∙ | Surj (WithZerosUnary d≥2) | [ eq ] =
    begin
        Fin.toℕ (fromℕ≤ d≥2) + zero
    ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ d≥2)) ⟩
        Fin.toℕ (fromℕ≤ d≥2)
    ≡⟨ toℕ-fromℕ≤ d≥2 ⟩
        suc zero
    ∎
toℕ-1+ {b} {d} {_} ∙ | Surj (WithZeros b≥2 d≥b) | [ eq ] =
    begin
        Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b)) + b * zero
    ≡⟨ cong (λ w → Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b)) + w) (*-right-zero b) ⟩
        Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b)) + zero
    ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b))) ⟩
        Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b))
    ≡⟨ toℕ-fromℕ≤ (≤-trans b≥2 d≥b) ⟩
        suc zero
    ∎
toℕ-1+ {b} {d} {_} ∙ | Surj (Zeroless b≥1 d≥b) | [ eq ] =
    begin
        suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)) + b * zero)
    ≡⟨ cong (λ w → suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b))) + w) (*-right-zero b) ⟩
        suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)) + zero)
    ≡⟨ +-right-identity (suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)))) ⟩
        suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)))
    ≡⟨ cong suc (toℕ-fromℕ≤ (≤-trans b≥1 d≥b)) ⟩
        suc zero
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
    -- digit+1-b x (SurjCond⇒b≥1 cond) p ∷ 1+ xs


-- digit+1-b-lemma : ∀ {b d} → (x : Digit d)
--     → b ≥ 1 → suc (Fin.toℕ x) ≡ d
--     → suc (Fin.toℕ x) ∸ b < d
--
-- digit+1-b : ∀ {b d} → (x : Digit d) → b ≥ 1 → suc (Fin.toℕ x) ≡ d → Fin d
-- digit+1-b {b} {d} x b≥1 p = fromℕ≤ {suc (Fin.toℕ x) ∸ b} (digit+1-b-lemma x b≥1 p)
--
-- digit+1 : ∀ {d} → (x : Digit d) → (¬p : suc (Fin.toℕ x) ≢ d) → Fin d
-- digit+1 x ¬p = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p)
-- Digit-toℕ x o + b * toℕ xs
-- digit+1-b x (SurjCond⇒b≥1 cond) p ∷ 1+ xs -- carry

toℕ-1+ {_} {d} {_} (x ∷ xs) | Surj (WithZerosUnary d≥2) | [ eq ] with full x
toℕ-1+ {_} {d} {_} (x ∷ xs) | Surj (WithZerosUnary d≥2) | [ eq ] | yes p =
    begin
        toℕ (digit+1-b x (SurjCond⇒b≥1 (WithZerosUnary d≥2)) p ∷ 1+ xs)
    ≡⟨ refl ⟩
        0 + Fin.toℕ (digit+1-b x (SurjCond⇒b≥1 (WithZerosUnary d≥2)) p) + 1 * toℕ (1+ xs)
    ≡⟨ cong (λ w → 0 + w + 1 * toℕ (1+ xs)) (toℕ-fromℕ≤ ((digit+1-b-lemma x (SurjCond⇒b≥1 (WithZerosUnary d≥2)) p))) ⟩
        0 + (suc (Fin.toℕ x) ∸ 1) + 1 * toℕ (1+ xs)
    ≡⟨ cong (λ w → 0 + (suc (Fin.toℕ x) ∸ 1) + 1 * w) (toℕ-1+ xs) ⟩
        0 + (suc (Fin.toℕ x) ∸ 1) + 1 * suc (toℕ xs)
    ≡⟨ cong (λ w → 0 + (suc (Fin.toℕ x) ∸ 1) + w) (*-comm 1 (suc (toℕ xs))) ⟩
        0 + (suc (Fin.toℕ x) ∸ 1) + (1 + toℕ xs * 1)
    ≡⟨ sym (+-assoc (0 + (suc (Fin.toℕ x) ∸ 1)) 1 (toℕ xs * 1)) ⟩
        0 + (suc (Fin.toℕ x) ∸ 1 + 1 + toℕ xs * 1)
    ≡⟨ cong (λ w → 0 + w + toℕ xs * 1) (+-comm (suc (Fin.toℕ x) ∸ 1) 1) ⟩
        0 + (1 + (suc (Fin.toℕ x) ∸ 1) + toℕ xs * 1)
    ≡⟨ cong (λ w → 0 + w + toℕ xs * 1) (m+n∸m≡n (                                               -- m+n∸m≡n
            start
                1
            ≤⟨ SurjCond⇒d≥b (WithZerosUnary d≥2) ⟩
                d
            ≤⟨ reflexive (sym p) ⟩
                suc (Fin.toℕ x)
            □)) ⟩
        0 + (suc (Fin.toℕ x + toℕ xs * 1))
    ≡⟨ cong (λ w → 0 + suc (Fin.toℕ x) + w) (*-comm (toℕ xs) 1) ⟩
        0 + suc (Fin.toℕ x + 1 * (toℕ xs))
    ∎
toℕ-1+ {_} {d} {_} (x ∷ xs) | Surj (WithZerosUnary d≥2) | [ eq ] | no ¬p = {!   !}
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (WithZeros b≥2 d≥b) | [ eq ] with full x
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (WithZeros b≥2 d≥b) | [ eq ] | yes p =
    begin
        toℕ (digit+1-b x (SurjCond⇒b≥1 (WithZeros b≥2 d≥b)) p ∷ 1+ xs)
    ≡⟨ refl ⟩
        0 + Fin.toℕ (digit+1-b x (SurjCond⇒b≥1 (WithZeros b≥2 d≥b)) p) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → 0 + w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ ((digit+1-b-lemma x (SurjCond⇒b≥1 (WithZeros b≥2 d≥b)) p))) ⟩
        0 + (suc (Fin.toℕ x) ∸ b) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → 0 + (suc (Fin.toℕ x) ∸ b) + b * w) (toℕ-1+ xs) ⟩
        0 + (suc (Fin.toℕ x) ∸ b) + b * suc (toℕ xs)
    ≡⟨ cong (λ w → 0 + (suc (Fin.toℕ x) ∸ b) + w) (*-comm b (suc (toℕ xs))) ⟩
        0 + (suc (Fin.toℕ x) ∸ b) + (b + toℕ xs * b)
    ≡⟨ sym (+-assoc (0 + (suc (Fin.toℕ x) ∸ b)) b (toℕ xs * b)) ⟩
        0 + (suc (Fin.toℕ x) ∸ b + b + toℕ xs * b)
    ≡⟨ cong (λ w → 0 + w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
        0 + (b + (suc (Fin.toℕ x) ∸ b) + toℕ xs * b)
    ≡⟨ cong (λ w → 0 + w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
            start
                b
            ≤⟨ SurjCond⇒d≥b (WithZeros b≥2 d≥b) ⟩
                d
            ≤⟨ reflexive (sym p) ⟩
                suc (Fin.toℕ x)
            □)) ⟩
        0 + (suc (Fin.toℕ x + toℕ xs * b))
    ≡⟨ cong (λ w → 0 + suc (Fin.toℕ x) + w) (*-comm (toℕ xs) b) ⟩
        0 + suc (Fin.toℕ x + b * (toℕ xs))
    ∎
toℕ-1+ (x ∷ xs) | Surj (WithZeros b≥2 d≥b) | [ eq ] | no ¬p = {!   !}
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (Zeroless b≥1 d≥b) | [ eq ] with full x
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (Zeroless b≥1 d≥b) | [ eq ] | yes p =
    begin
        toℕ (digit+1-b x (SurjCond⇒b≥1 (Zeroless b≥1 d≥b)) p ∷ 1+ xs)
    ≡⟨ refl ⟩
        1 + Fin.toℕ (digit+1-b x (SurjCond⇒b≥1 (Zeroless b≥1 d≥b)) p) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → 1 + w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ ((digit+1-b-lemma x (SurjCond⇒b≥1 (Zeroless b≥1 d≥b)) p))) ⟩
        1 + (suc (Fin.toℕ x) ∸ b) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → 1 + (suc (Fin.toℕ x) ∸ b) + b * w) (toℕ-1+ xs) ⟩
        1 + (suc (Fin.toℕ x) ∸ b) + b * suc (toℕ xs)
    ≡⟨ cong (λ w → 1 + (suc (Fin.toℕ x) ∸ b) + w) (*-comm b (suc (toℕ xs))) ⟩
        1 + (suc (Fin.toℕ x) ∸ b) + (b + toℕ xs * b)
    ≡⟨ sym (+-assoc (1 + (suc (Fin.toℕ x) ∸ b)) b (toℕ xs * b)) ⟩
        1 + (suc (Fin.toℕ x) ∸ b + b + toℕ xs * b)
    ≡⟨ cong (λ w → 1 + w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
        1 + (b + (suc (Fin.toℕ x) ∸ b) + toℕ xs * b)
    ≡⟨ cong (λ w → 1 + w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
            start
                b
            ≤⟨ SurjCond⇒d≥b (Zeroless b≥1 d≥b) ⟩
                d
            ≤⟨ reflexive (sym p) ⟩
                suc (Fin.toℕ x)
            □)) ⟩
        1 + (suc (Fin.toℕ x + toℕ xs * b))
    ≡⟨ cong (λ w → 1 + suc (Fin.toℕ x) + w) (*-comm (toℕ xs) b) ⟩
        1 + suc (Fin.toℕ x + b * (toℕ xs))
    ∎
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (Zeroless b≥1 d≥b) | [ eq ] | no ¬p = {!   !}

-- toℕ-1+ {b} {d} {o} (x ∷ xs) | Surj cond | [ eq ] with full x
-- toℕ-1+ (x ∷ xs) | Surj (WithZerosUnary d≥2) | [ eq ] | yes p = {!   !}
--     -- begin
--     --     toℕ (digit+1-b x {!   !} p ∷ {! 1+ xs  !})
--     -- ≡⟨ {!   !} ⟩
--     --     {!   !}
--     -- ≡⟨ {!   !} ⟩
--     --     {!   !}
--     -- ≡⟨ {!   !} ⟩
--     --     {!   !}
--     -- ≡⟨ {!   !} ⟩
--     --     Fin.toℕ (fromℕ≤ {suc (Fin.toℕ x) ∸ 1} ((digit+1-b-lemma x (SurjCond⇒b≥1 {!WithZerosUnary d≥2   !}) p))) + 1 * toℕ (1+ xs)
--     -- ≡⟨ cong (λ w → w + 1 * toℕ (1+ xs)) (toℕ-fromℕ≤ ((digit+1-b-lemma x (s≤s z≤n) p))) ⟩
--     --     suc (Fin.toℕ x) ∸ 1 + 1 * toℕ (1+ xs)
--     -- ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ 1 + 1 * w) (toℕ-1+ xs) ⟩
--     --     suc (Fin.toℕ x) ∸ 1 + 1 * suc (toℕ xs)
--     -- ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ 1 + w) (*-comm 1 (suc (toℕ xs))) ⟩
--     --     Fin.toℕ x + suc (toℕ xs * 1)
--     -- ≡⟨ sym (+-assoc (suc (Fin.toℕ x) ∸ 1) 1 (toℕ xs * 1)) ⟩
--     --     Fin.toℕ x + 1 + toℕ xs * 1
--     -- ≡⟨ cong (λ w → w + toℕ xs * 1) (+-comm (suc (Fin.toℕ x) ∸ 1) 1) ⟩
--     --     1 + (suc (Fin.toℕ x) ∸ 1) + toℕ xs * 1
--     -- ≡⟨ cong (λ w → w + toℕ xs * 1) (m+n∸m≡n (                                               -- m+n∸m≡n
--     --         start
--     --             1
--     --         ≤⟨ ≤⇒pred≤ 2 d d≥2 ⟩
--     --             d
--     --         ≤⟨ reflexive (sym p) ⟩
--     --             suc (Fin.toℕ x)
--     --         □)) ⟩
--     --     suc (Fin.toℕ x + toℕ xs * 1)
--     -- ≡⟨ cong (λ w → suc (Fin.toℕ x) + w) (*-comm (toℕ xs) 1) ⟩
--     --     suc (Fin.toℕ x + (toℕ xs + zero))
--     -- ∎
-- toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (WithZeros b≥2 d≥b) | [ eq ] | yes p =
--     begin
--         Fin.toℕ (fromℕ≤ {suc (Fin.toℕ x) ∸ b} ((digit+1-b-lemma x (s≤s z≤n) p))) + b * toℕ (1+ xs)
--     ≡⟨ cong (λ w → w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ ((digit+1-b-lemma x (s≤s z≤n) p))) ⟩
--         suc (Fin.toℕ x) ∸ b + b * toℕ (1+ xs)
--     ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ b + b * w) (toℕ-1+ xs) ⟩
--         suc (Fin.toℕ x) ∸ b + b * suc (toℕ xs)
--     ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ b + w) (*-comm b (suc (toℕ xs))) ⟩
--         suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b)
--     ≡⟨ sym (+-assoc (suc (Fin.toℕ x) ∸ b) b (toℕ xs * b)) ⟩
--         suc (Fin.toℕ x) ∸ b + b + toℕ xs * b
--     ≡⟨ cong (λ w → w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
--         b + (suc (Fin.toℕ x) ∸ b) + toℕ xs * b
--     ≡⟨ cong (λ w → w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
--             start
--                 b
--             ≤⟨ d≥b ⟩
--                 d
--             ≤⟨ reflexive (sym p) ⟩
--                 suc (Fin.toℕ x)
--             □)) ⟩
--         suc (Fin.toℕ x) + toℕ xs * b
--     ≡⟨ cong (λ w → suc (Fin.toℕ x) + w) (*-comm (toℕ xs) b) ⟩
--         suc (Fin.toℕ x + b * toℕ xs)
--     ∎
-- toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (Zeroless b≥1 d≥b) | [ eq ] | yes p =
--     begin
--         Fin.toℕ (fromℕ≤ {suc (suc (Fin.toℕ x) ∸ b)} ((digit+1-b-lemma x (s≤s z≤n) p))) + b * toℕ (1+ xs)
--     ≡⟨ cong (λ w → suc w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ ((digit+1-b-lemma x (s≤s z≤n) p))) ⟩
--         suc (suc (Fin.toℕ x) ∸ b) + b * toℕ (1+ xs)
--     ≡⟨ cong (λ w → suc (suc (Fin.toℕ x) ∸ b) + b * w) (toℕ-1+ xs) ⟩
--         suc (suc (Fin.toℕ x) ∸ b + b * suc (toℕ xs))
--     ≡⟨ cong (λ w → suc (suc (Fin.toℕ x) ∸ b) + w) (*-comm b (suc (toℕ xs))) ⟩
--         suc (suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b))
--     ≡⟨ sym (+-assoc (suc (suc (Fin.toℕ x) ∸ b)) b (toℕ xs * b)) ⟩
--         suc (suc (Fin.toℕ x) ∸ b + b + toℕ xs * b)
--     ≡⟨ cong (λ w → suc w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
--         suc (b + (suc (Fin.toℕ x) ∸ b) + toℕ xs * b)
--     ≡⟨ cong (λ w → suc w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
--             start
--                 b
--             ≤⟨ d≥b ⟩
--                 d
--             ≤⟨ reflexive (sym p) ⟩
--                 suc (Fin.toℕ x)
--             □)) ⟩
--         suc (suc (Fin.toℕ x + toℕ xs * b))
--     ≡⟨ cong (λ w → suc (suc (Fin.toℕ x)) + w) (*-comm (toℕ xs) b) ⟩
--         suc (suc (Fin.toℕ x + b * toℕ xs))
--     ∎
-- toℕ-1+ (x ∷ xs) | Surj cond | [ eq ] | no ¬p = {!   !}
toℕ-1+ {b} {d} {o} {surjCond , ()} xs | NonSurj reason | [ eq ]

--
-- toℕ-1+ : ∀ {b d o}
--     → {✓ : notSpurious b d o}
--     → (xs : Num b d o)
--     → toℕ (1+ xs) ≡ suc (toℕ xs)
-- toℕ-1+ {b} {d} {o} xs   with surjectionView b d o
-- toℕ-1+ {b} {d}     ∙    | WithZero b≥1 d≥2 b≤d  =
--     begin
--         Fin.toℕ (fromℕ≤ d≥2) + b * zero
--     ≡⟨ cong (λ x → Fin.toℕ (fromℕ≤ d≥2) + x) (*-right-zero b) ⟩
--         Fin.toℕ (fromℕ≤ d≥2) + zero
--     ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ d≥2)) ⟩
--         Fin.toℕ (fromℕ≤ d≥2)
--     ≡⟨ toℕ-fromℕ≤ d≥2 ⟩
--         suc zero
--     ∎
-- toℕ-1+ {b} {d} (x ∷ xs) | WithZero b≥1 d≥2 b≤d with full x
-- toℕ-1+ {b} {d} (x ∷ xs) | WithZero b≥1 d≥2 b≤d | yes p =
--     begin
--         Fin.toℕ {d} (digit+1-b x b≥1 p) + b * toℕ (1+ xs)
--     ≡⟨ cong (λ w → w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ (digit+1-b-lemma x b≥1 p)) ⟩    -- toℕ-fromℕ≤
--         suc (Fin.toℕ x) ∸ b + b * toℕ (1+ xs)
--     ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ b + b * w) (toℕ-1+ {✓ = WithZero≢Spurious b≥1 d≥2 b≤d} xs) ⟩        -- induction
--         suc (Fin.toℕ x) ∸ b + b * suc (toℕ xs)
--     ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ b + w) (*-comm b (suc (toℕ xs))) ⟩
--         suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b)
--     ≡⟨ sym (+-assoc (suc (Fin.toℕ x) ∸ b) b (toℕ xs * b)) ⟩
--         suc (Fin.toℕ x) ∸ b + b + toℕ xs * b
--     ≡⟨ cong (λ w → w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
--         b + (suc (Fin.toℕ x) ∸ b) + toℕ xs * b
--     ≡⟨ cong (λ w → w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
--             start
--                 b
--             ≤⟨ b≤d ⟩
--                 d
--             ≤⟨ reflexive (sym p) ⟩
--                 suc (Fin.toℕ x)
--             □)) ⟩
--         suc (Fin.toℕ x) + toℕ xs * b
--     ≡⟨ cong (λ w → suc (Fin.toℕ x) + w) (*-comm (toℕ xs) b) ⟩
--         suc (Fin.toℕ x + b * toℕ xs)
--     ∎
-- toℕ-1+ {b} {d} (x ∷ xs) | WithZero b≥1 d≥2 b≤d | no ¬p =
--     cong (λ w → w + b * toℕ xs) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p))
-- toℕ-1+ {b} {d} ∙        | Zeroless b≥1 d≥1 b≤d =
--     begin
--         suc (Fin.toℕ (fromℕ≤ d≥1) + b * zero)
--     ≡⟨ cong (λ x → suc (Fin.toℕ (fromℕ≤ d≥1)) + x) (*-right-zero b) ⟩
--         suc (Fin.toℕ (fromℕ≤ d≥1) + zero)
--     ≡⟨ cong (λ x → suc x + 0) (toℕ-fromℕ≤ d≥1) ⟩
--         suc zero
--     ∎
-- toℕ-1+ {b} {d} (x ∷ xs) | Zeroless b≥1 d≥1 b≤d with full x
-- toℕ-1+ {b} {d} (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | yes p =
--     begin
--         suc (Fin.toℕ (digit+1-b x b≥1 p)) + b * toℕ (1+ xs)
--     ≡⟨ cong (λ w → suc w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ (digit+1-b-lemma x b≥1 p)) ⟩    -- toℕ-fromℕ≤
--         suc (suc (Fin.toℕ x) ∸ b) + b * toℕ (1+ xs)
--     ≡⟨ cong (λ w → suc (suc (Fin.toℕ x) ∸ b) + b * w) (toℕ-1+ {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d} xs) ⟩      -- induction
--         suc (suc (Fin.toℕ x) ∸ b + b * suc (toℕ xs))
--     ≡⟨ cong (λ w → suc (suc (Fin.toℕ x) ∸ b + w)) (*-comm b (suc (toℕ xs))) ⟩
--         suc (suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b))
--     ≡⟨  sym (+-assoc (suc (suc (Fin.toℕ x) ∸ b)) b (toℕ xs * b)) ⟩
--         suc (suc (Fin.toℕ x) ∸ b + b + toℕ xs * b)
--     ≡⟨ cong (λ w → suc w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
--         suc (b + (suc (Fin.toℕ x) ∸ b)) + toℕ xs * b
--     ≡⟨ cong (λ w → suc w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
--             start
--                 b
--             ≤⟨ b≤d ⟩
--                 d
--             ≤⟨ reflexive (sym p) ⟩
--                 suc (Fin.toℕ x)
--             □)) ⟩
--         suc (suc (Fin.toℕ x + toℕ xs * b))
--     ≡⟨ cong (λ w → suc (suc (Fin.toℕ x + w))) (*-comm (toℕ xs) b) ⟩
--         suc (suc (Fin.toℕ x + b * toℕ xs))
--     ∎
-- toℕ-1+ {b} {d} (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | no ¬p =
--     cong (λ w → suc w + b * toℕ xs) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p))
-- toℕ-1+ {✓ = claim} xs      | Spurious reason = contradiction refl (claim reason)
--
--
-- 1+-fromℕ : ∀ {b d o}
--     → {✓ : notSpurious b d o}
--     → (n : ℕ)
--     → 1+ (fromℕ {b} {d} {o} n) ≡ fromℕ (suc n)
-- 1+-fromℕ {b} {d} {o} n with surjectionView b d o | inspect (surjectionView b d) o
-- 1+-fromℕ             n | WithZero b≥1 d≥2 b≤d | [ eq ] rewrite eq = refl
-- 1+-fromℕ             n | Zeroless b≥1 d≥1 b≤d | [ eq ] rewrite eq = refl
-- 1+-fromℕ {✓ = claim} n | Spurious reason      | [ eq ] = contradiction refl (claim reason)
--
-- toℕ-fromℕ : ∀ {b d o}
--     → {✓ : notSpurious b d o}
--     → (n : ℕ)
--     → toℕ (fromℕ {b} {d} {o} n) ≡ n
-- toℕ-fromℕ {b} {d} {o} n       with surjectionView b d o
-- toℕ-fromℕ {b} {d}     zero    | WithZero b≥1 d≥2 b≤d = refl
-- toℕ-fromℕ {b} {d}     (suc n) | WithZero b≥1 d≥2 b≤d =
--     begin
--         toℕ (1+ (fromℕ {b} {d} n))
--     ≡⟨ toℕ-1+ {✓ = WithZero≢Spurious b≥1 d≥2 b≤d} (fromℕ {b} {d} n) ⟩
--         suc (toℕ (fromℕ {b} {d} n))
--     ≡⟨ cong suc (toℕ-fromℕ {b} {d} {✓ = WithZero≢Spurious b≥1 d≥2 b≤d} n) ⟩
--         suc n
--     ∎
-- toℕ-fromℕ {b} {d}     zero    | Zeroless b≥1 d≥1 b≤d = refl
-- toℕ-fromℕ {b} {d}     (suc n) | Zeroless b≥1 d≥1 b≤d =
--     begin
--         toℕ (1+ (fromℕ {b} {d} n))
--     ≡⟨ toℕ-1+ {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d} (fromℕ {b} {d} n) ⟩
--         suc (toℕ (fromℕ {b} {d} n))
--     ≡⟨ cong suc (toℕ-fromℕ {b} {d} {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d} n) ⟩
--         suc n
--     ∎
-- toℕ-fromℕ {✓ = claim}   n     | Spurious reason = contradiction refl (claim reason)
--
--
--
-- ------------------------------------------------------------------------
-- -- Lemmata for proving Spurious cases not surjective
-- ------------------------------------------------------------------------
--
-- lemma1 : ∀ {d o} → (xs : Num 0 d o) → toℕ xs ≢ suc (o + d)
-- lemma1 {d} {o} ∙        ()
-- lemma1 {d} {o} (x ∷ xs) p =
--     contradiction p (<⇒≢ ⟦x∷xs⟧<1+o+d)
--     where
--         ⟦x∷xs⟧<1+o+d : o + Fin.toℕ x + 0 < suc (o + d)
--         ⟦x∷xs⟧<1+o+d = s≤s $
--             start
--                 o + Fin.toℕ x + zero
--             ≤⟨ reflexive (+-right-identity (o + Fin.toℕ x)) ⟩
--                 o + Fin.toℕ x
--             ≤⟨ ≤-sucs o (
--                 start
--                     Fin.toℕ x
--                 ≤⟨ n≤1+n (Fin.toℕ x) ⟩
--                     suc (Fin.toℕ x)
--                 ≤⟨ bounded x ⟩
--                     d
--                 □
--             )⟩
--                 o + d
--             □
--
-- lemma2 : ∀ {b o} → (xs : Num b 0 o) → toℕ xs ≢ 1
-- lemma2 ∙         ()
-- lemma2 (() ∷ xs)
--
-- lemma3 : ∀ {b d o} → o ≥ 2 → (xs : Num b d o) → toℕ xs ≢ 1
-- lemma3                   o≥2      ∙        ()
-- lemma3 {o = 0}           ()       (x ∷ xs) p
-- lemma3 {o = 1}           (s≤s ()) (x ∷ xs) p
-- lemma3 {o = suc (suc o)} o≥2      (x ∷ xs) ()
--
-- lemma4 : (xs : Num 1 1 0) → toℕ xs ≢ 1
-- lemma4 ∙ ()
-- lemma4 (z ∷ xs) p = contradiction (begin
--         toℕ xs
--     ≡⟨ sym (+-right-identity (toℕ xs)) ⟩
--         toℕ xs + zero
--     ≡⟨ p ⟩
--         suc zero
--     ∎) (lemma4 xs)
-- lemma4 (s () ∷ xs)
--
-- lemma5 : ∀ {b d o} → d ≥ 1 → b ≰ d → (xs : Num b d o) → toℕ xs ≢ o + d
-- lemma5 {_} {_} {o} d≥1 b≰d ∙        = <⇒≢ (≤-steps o d≥1)
-- lemma5 {b} {d} {o} d≥1 b≰d (x ∷ xs) p with toℕ xs ≤? 0
-- lemma5 {b} {d} {o} d≥1 b≰d (x ∷ xs) p | yes q =
--     contradiction p (<⇒≢ ⟦x∷xs⟧>o+d)
--     where
--         ⟦xs⟧≡0 : toℕ xs ≡ 0
--         ⟦xs⟧≡0 = ≤0⇒≡0 (toℕ xs) q
--         ⟦x∷xs⟧>o+d : o + Fin.toℕ x + b * toℕ xs < o + d
--         ⟦x∷xs⟧>o+d = start
--                 suc (o + Fin.toℕ x + b * toℕ xs)
--             ≤⟨ reflexive (begin
--                     suc (o + Fin.toℕ x + b * toℕ xs)
--                 ≡⟨ cong (λ w → suc (o + Fin.toℕ x + b * w)) ⟦xs⟧≡0 ⟩
--                     suc (o + Fin.toℕ x + b * zero)
--                 ≡⟨ cong (λ w → suc (o + Fin.toℕ x + w)) (*-right-zero b) ⟩
--                     suc (o + Fin.toℕ x + zero)
--                 ≡⟨ +-right-identity (suc (o + Fin.toℕ x)) ⟩
--                     suc (o + Fin.toℕ x)
--                 ≡⟨ sym (+-suc o (Fin.toℕ x)) ⟩
--                     o + suc (Fin.toℕ x)
--                 ∎) ⟩
--                 o + suc (Fin.toℕ x)
--             ≤⟨ ≤-sucs o (bounded x) ⟩
--                 o + d
--             □
--
-- lemma5 {b} {d} {o} d≥1 b≰d (x ∷ xs) p | no ¬q =
--     contradiction p (>⇒≢ ⟦x∷xs⟧>o+d)
--     where
--         ⟦x∷xs⟧>o+d : o + Fin.toℕ x + b * toℕ xs > o + d
--         ⟦x∷xs⟧>o+d = start
--                 suc (o + d)
--             ≤⟨ reflexive (sym (+-suc o d)) ⟩
--                 o + suc d
--             ≤⟨ ≤-sucs o (
--                 start
--                     suc d
--                 ≤⟨ ≰⇒> b≰d ⟩
--                     b
--                 ≤⟨ reflexive (sym (*-right-identity b)) ⟩
--                     b * 1
--                 ≤⟨ _*-mono_ {b} {b} {1} {toℕ xs} ≤-refl (≰⇒> ¬q) ⟩
--                     b * toℕ xs
--                 ≤⟨ n≤m+n (Fin.toℕ x) (b * toℕ xs) ⟩
--                     Fin.toℕ x + b * toℕ xs
--                 □
--             ) ⟩
--                 o + (Fin.toℕ x + b * toℕ xs)
--             ≤⟨ reflexive (sym (+-assoc o (Fin.toℕ x) (b * toℕ xs))) ⟩
--                 o + Fin.toℕ x + b * toℕ xs
--             □
--
-- Spurious⇏Surjective : ∀ {b} {d} {o} → WhySpurious b d o → ¬ (Surjective (Num⟶ℕ b d o))
-- Spurious⇏Surjective {_} {d} {o} Base≡0              claim =
--     lemma1 (from claim ⟨$⟩ suc o + d) (right-inverse-of claim (suc (o + d)))
-- Spurious⇏Surjective NoDigits            claim =
--     lemma2      (from claim ⟨$⟩ 1)    (right-inverse-of claim 1)
-- Spurious⇏Surjective (Offset≥2 p)        claim =
--     lemma3 p    (from claim ⟨$⟩ 1)    (right-inverse-of claim 1)
-- Spurious⇏Surjective UnaryWithOnly0s     claim =
--     lemma4     (from claim ⟨$⟩ 1)     (right-inverse-of claim 1)
-- Spurious⇏Surjective {_} {d} {o} (NotEnoughDigits p q) claim =
--     lemma5 p q (from claim ⟨$⟩ o + d) (right-inverse-of claim (o + d))
--
-- Surjective? : ∀ b d o → Dec (Surjective (Num⟶ℕ b d o))
-- Surjective? b d o with surjectionView b d o
-- Surjective? b d 0 | WithZero b≥1 d≥2 b≤d = yes (record
--     { from = ℕ⟶Num b d 0
--     ; right-inverse-of = toℕ-fromℕ {b} {d} {✓ = WithZero≢Spurious b≥1 d≥2 b≤d}
--     })
-- Surjective? b d 1 | Zeroless b≥1 d≥1 b≤d = yes (record
--     { from = ℕ⟶Num b d 1
--     ; right-inverse-of = toℕ-fromℕ {b} {d} {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d}
--     })
-- Surjective? b d _ | Spurious reason = no (Spurious⇏Surjective reason)
--
-- Surjective⇒base≥1 : ∀ {b} {d} {o} → Surjective (Num⟶ℕ b d o) → b ≥ 1
-- Surjective⇒base≥1 {zero} {d} {o} surj = contradiction
--     (right-inverse-of surj (suc (o + d)))       -- : toℕ (from surj ⟨$⟩ suc (o + d)) ≡ suc (o + d)
--     (lemma1 (_⟨$⟩_ (from surj) (suc (o + d))))  -- : toℕ (from surj ⟨$⟩ suc (o + d)) ≢ suc (o + d)
-- Surjective⇒base≥1 {suc b} surj = s≤s z≤n
--
-- Surjective⇒d≥1 : ∀ {b} {d} {o} → Surjective (Num⟶ℕ b d o) → d ≥ 1
-- Surjective⇒d≥1 {d = zero} surj = contradiction
--     (right-inverse-of surj 1)           -- : toℕ (from surj ⟨$⟩ 1) ≡ 1
--     (lemma2 (from surj ⟨$⟩ 1))          -- : toℕ (from surj ⟨$⟩ 1) ≢ 1
-- Surjective⇒d≥1 {d = suc d} surj = s≤s z≤n
--
-- Surjective⇒b≤d : ∀ {b} {d} {o} → Surjective (Num⟶ℕ b d o) → b ≤ d
-- Surjective⇒b≤d {_} {zero} {_} surj = contradiction
--     (Surjective⇒d≥1 surj)               -- : d ≥ 1
--     (λ ())                              -- : d ≱ 1
-- Surjective⇒b≤d {b} {suc d} {o} surj with b ≤? suc d
-- Surjective⇒b≤d {b} {suc d} {o} surj | yes p = p
-- Surjective⇒b≤d {b} {suc d} {o} surj | no ¬p = contradiction
--     (right-inverse-of surj (o + suc d))             -- : toℕ (from surj ⟨$⟩ (o + suc d)) ≡ (o + suc d)
--     (lemma5 (s≤s z≤n) ¬p (from surj ⟨$⟩ o + suc d)) -- : toℕ (from surj ⟨$⟩ (o + suc d)) ≢ (o + suc d)
