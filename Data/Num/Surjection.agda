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
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

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

IsSurjective : ℕ → ℕ → ℕ → Set
IsSurjective b d o with surjectionView b d o
IsSurjective b d o | Surj    _ = ⊤
IsSurjective b d o | NonSurj _ = ⊥

SurjCond⇒b≥1 : ∀ {b d o} → SurjCond b d o → b ≥ 1
SurjCond⇒b≥1 (WithZerosUnary d≥2)      = s≤s z≤n
SurjCond⇒b≥1 (WithZeros (s≤s b≥1) d≥b) = s≤s z≤n
SurjCond⇒b≥1 (Zeroless b≥1 d≥b)        = b≥1

SurjCond⇒d≥b : ∀ {b d o} → SurjCond b d o → d ≥ b
SurjCond⇒d≥b (WithZerosUnary (s≤s d≥1)) = s≤s z≤n
SurjCond⇒d≥b (WithZeros b≥2 d≥b)        = d≥b
SurjCond⇒d≥b (Zeroless b≥1 d≥b)         = d≥b

SurjCond⇒IsSurj : ∀ {b d o} → SurjCond b d o → IsSurjective b d o
SurjCond⇒IsSurj {b} {d} {o} cond with surjectionView b d o
SurjCond⇒IsSurj cond | Surj x = tt
SurjCond⇒IsSurj (WithZeros () d≥b)        | NonSurj Base≡0
SurjCond⇒IsSurj (Zeroless () d≥b)         | NonSurj Base≡0
SurjCond⇒IsSurj (WithZerosUnary ())       | NonSurj NoDigits
SurjCond⇒IsSurj (WithZeros () z≤n)        | NonSurj NoDigits
SurjCond⇒IsSurj (Zeroless () z≤n)         | NonSurj NoDigits
SurjCond⇒IsSurj (WithZerosUnary _)        | NonSurj (Offset≥2 ())
SurjCond⇒IsSurj (WithZeros _ _)           | NonSurj (Offset≥2 ())
SurjCond⇒IsSurj (Zeroless _ _)            | NonSurj (Offset≥2 (s≤s ()))
SurjCond⇒IsSurj (WithZerosUnary (s≤s ())) | NonSurj UnaryWithOnlyZeros
SurjCond⇒IsSurj (WithZeros (s≤s ()) _)    | NonSurj UnaryWithOnlyZeros
SurjCond⇒IsSurj (WithZerosUnary _)        | NonSurj (NotEnoughDigits d≥1 d≱1) = contradiction d≥1 d≱1
SurjCond⇒IsSurj (WithZeros _ d≥b)         | NonSurj (NotEnoughDigits _ d≱b) = contradiction d≥b d≱b
SurjCond⇒IsSurj (Zeroless _ d≥b)          | NonSurj (NotEnoughDigits _ d≱b) = contradiction d≥b d≱b

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
n+ zero xs = xs
n+ (suc n) xs = 1+ (n+ n xs)

fromℕ : ∀ {b d o} → ℕ → Num b d o
fromℕ {b} {d} {o} n with surjectionView b d o
fromℕ n |    Surj x = n+ n ∙
fromℕ n | NonSurj x = ∙


-- fromℕ that preserves equality
ℕ⟶Num : ∀ b d o → setoid ℕ ⟶ setoid (Num b d o)
ℕ⟶Num b d o = record
    { _⟨$⟩_ = fromℕ
    ; cong = cong fromℕ
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

------------------------------------------------------------------------
-- toℕ-1+ : toℕ (1+ xs) ≡ suc (toℕ xs)
------------------------------------------------------------------------

toℕ-1+-x∷xs-full-lemma : ∀ {b d o}
    → (x : Digit d) → (xs : Num b d o)
    → (cond : SurjCond b d o)
    → (p : suc (Fin.toℕ x) ≡ d)
    → (toℕ-1+-xs : toℕ (1+ xs) ≡ suc (toℕ xs))
    → toℕ (digit+1-b x (SurjCond⇒b≥1 cond) p ∷ 1+ xs) ≡ suc (toℕ (x ∷ xs))
toℕ-1+-x∷xs-full-lemma {b} {d} {o} x xs cond p toℕ-1+-xs =
    begin
        toℕ (digit+1-b x (SurjCond⇒b≥1 cond) p ∷ 1+ xs)
    -- toℕ-fromℕ≤ : toℕ (fromℕ≤ m<n) ≡ m
    ≡⟨ cong (λ w → o + w + toℕ (1+ xs) * b) (toℕ-fromℕ≤ ((digit+1-b-lemma x (SurjCond⇒b≥1 cond) p))) ⟩
        o + (suc (Fin.toℕ x) ∸ b) + toℕ (1+ xs) * b
    -- induction hypothesis
    ≡⟨ cong (λ w → o + (suc (Fin.toℕ x) ∸ b) + w * b) toℕ-1+-xs ⟩
        o + (suc (Fin.toℕ x) ∸ b) + (b + toℕ xs * b)
    ≡⟨ +-assoc o (suc (Fin.toℕ x) ∸ b) (b + toℕ xs * b) ⟩
        o + (suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b))
    ≡⟨ cong (λ w → o + w) (sym (+-assoc (suc (Fin.toℕ x) ∸ b) b (toℕ xs * b))) ⟩
        o + (suc (Fin.toℕ x) ∸ b + b + toℕ xs * b)
    ≡⟨ cong (λ w → o + (w + toℕ xs * b)) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
        o + (b + (suc (Fin.toℕ x) ∸ b) + toℕ xs * b)
    -- m+n∸m≡n : m + (n ∸ m) ≡ n
    ≡⟨ cong (λ w → o + (w + toℕ xs * b)) (m+n∸m≡n (
            start
                b
            ≤⟨ SurjCond⇒d≥b cond ⟩
                d
            ≤⟨ reflexive (sym p) ⟩
                suc (Fin.toℕ x)
            □)) ⟩
        o + suc (Fin.toℕ x + toℕ xs * b)
    ≡⟨ +-suc o (Fin.toℕ x + toℕ xs * b) ⟩
        suc (o + (Fin.toℕ x + toℕ xs * b))
    ≡⟨ cong suc (sym (+-assoc o (Fin.toℕ x) (toℕ xs * b))) ⟩
        suc (o + Fin.toℕ x + toℕ xs * b)
    ∎

toℕ-1+-x∷xs-not-full-lemma : ∀ {b d o}
    → (x : Digit d) → (xs : Num b d o)
    → (¬p : suc (Fin.toℕ x) ≢ d)
    → toℕ (digit+1 x ¬p ∷ xs) ≡ suc (toℕ (x ∷ xs))
toℕ-1+-x∷xs-not-full-lemma {b} {d} {o} x xs ¬p =
    begin
        o + Fin.toℕ (fromℕ≤ (≤∧≢⇒< (bounded x) ¬p)) + toℕ xs * b
    -- toℕ-fromℕ≤
    ≡⟨ cong (λ w → o + w + toℕ xs * b) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p)) ⟩
        o + suc (Fin.toℕ x) + toℕ xs * b
    ≡⟨ +-assoc o (suc (Fin.toℕ x)) (toℕ xs * b) ⟩
        o + suc (Fin.toℕ x + toℕ xs * b)
    ≡⟨ +-suc o (Fin.toℕ x + toℕ xs * b) ⟩
        suc (o + (Fin.toℕ x + toℕ xs * b))
    ≡⟨ cong suc (sym (+-assoc o (Fin.toℕ x) (toℕ xs * b))) ⟩
        suc (o + Fin.toℕ x + toℕ xs * b)
    ∎


toℕ-1+ : ∀ {b d o}
    → {isSurjective : IsSurjective b d o}
    → (xs : Num b d o)
    → toℕ (1+ xs) ≡ suc (toℕ xs)
toℕ-1+ {b} {d} {o} xs with surjectionView b d o
toℕ-1+ {_} {d} {_} ∙ | Surj (WithZerosUnary d≥2) =
    begin
        Fin.toℕ (fromℕ≤ d≥2) + zero
    ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ d≥2)) ⟩
        Fin.toℕ (fromℕ≤ d≥2)
    ≡⟨ toℕ-fromℕ≤ d≥2 ⟩
        suc zero
    ∎
toℕ-1+ {b} {d} {_} ∙ | Surj (WithZeros b≥2 d≥b) =
    begin
        Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b)) + zero * b
    ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b))) ⟩
        Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b))
    ≡⟨ toℕ-fromℕ≤ (≤-trans b≥2 d≥b) ⟩
        suc zero
    ∎
toℕ-1+ {b} {d} {_} ∙ | Surj (Zeroless b≥1 d≥b) =
    begin
        suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)) + zero)
    ≡⟨ +-right-identity (suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)))) ⟩
        suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)))
    ≡⟨ cong suc (toℕ-fromℕ≤ (≤-trans b≥1 d≥b)) ⟩
        suc zero
    ∎
toℕ-1+ {_} {d} {_} (x ∷ xs) | Surj (WithZerosUnary d≥2) with full x
toℕ-1+ {_} {d} {_} (x ∷ xs) | Surj (WithZerosUnary d≥2) | yes p = toℕ-1+-x∷xs-full-lemma x xs (WithZerosUnary d≥2) p (toℕ-1+ {isSurjective = SurjCond⇒IsSurj (WithZerosUnary d≥2)} xs)
toℕ-1+ {_} {d} {_} (x ∷ xs) | Surj (WithZerosUnary d≥2) | no ¬p = toℕ-1+-x∷xs-not-full-lemma x xs ¬p
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (WithZeros b≥2 d≥b)  with full x
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (WithZeros b≥2 d≥b)  | yes p = toℕ-1+-x∷xs-full-lemma x xs (WithZeros b≥2 d≥b) p (toℕ-1+ {isSurjective = SurjCond⇒IsSurj (WithZeros b≥2 d≥b)} xs)
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (WithZeros b≥2 d≥b)  | no ¬p = toℕ-1+-x∷xs-not-full-lemma x xs ¬p
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (Zeroless b≥1 d≥b)   with full x
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (Zeroless b≥1 d≥b)   | yes p = toℕ-1+-x∷xs-full-lemma x xs (Zeroless b≥1 d≥b) p (toℕ-1+ {isSurjective = SurjCond⇒IsSurj (Zeroless b≥1 d≥b)} xs)
toℕ-1+ {b} {d} {_} (x ∷ xs) | Surj (Zeroless b≥1 d≥b)   | no ¬p = toℕ-1+-x∷xs-not-full-lemma x xs ¬p
toℕ-1+ {isSurjective = ()} xs | NonSurj reason

------------------------------------------------------------------------
-- toℕ-n+ : toℕ (n+ n xs) ≡ n + (toℕ xs)
------------------------------------------------------------------------

toℕ-n+ : ∀ {b d o}
    → {isSurjective : IsSurjective b d o}
    → (n : ℕ)
    → (xs : Num b d o)
    → toℕ (n+ n xs) ≡ n + (toℕ xs)
toℕ-n+ {b} {d} {o} n xs with surjectionView b d o
toℕ-n+ zero xs | Surj cond = refl
toℕ-n+ (suc n) xs | Surj cond =
    begin
        toℕ (n+ (suc n) xs)
    ≡⟨ refl ⟩
        toℕ (1+ (n+ n xs))
    ≡⟨ toℕ-1+ {isSurjective = SurjCond⇒IsSurj cond} (n+ n xs) ⟩
        suc (toℕ (n+ n xs))
    ≡⟨ cong suc (toℕ-n+ {isSurjective = SurjCond⇒IsSurj cond} n xs) ⟩
        suc (n + toℕ xs)
    ∎
toℕ-n+ {isSurjective = ()} n xs | NonSurj reason

------------------------------------------------------------------------
-- toℕ-fromℕ : toℕ (fromℕ n) ≡ n
------------------------------------------------------------------------

toℕ-fromℕ : ∀ {b d o}
    → {isSurjective : IsSurjective b d o}
    → (n : ℕ)
    → toℕ (fromℕ {b} {d} {o} n) ≡ n
toℕ-fromℕ {b} {d} {o} n       with surjectionView b d o
toℕ-fromℕ             zero    | Surj (WithZerosUnary d≥2) = refl
toℕ-fromℕ {_} {d} {_} (suc n) | Surj (WithZerosUnary d≥2) =
    begin
        toℕ (1+ (n+ {1} {d} {0} n ∙))
    ≡⟨ toℕ-1+ {1} {d} {0} {SurjCond⇒IsSurj (WithZerosUnary d≥2)} (n+ n ∙) ⟩
        suc (toℕ (n+ n ∙))
    ≡⟨ cong suc (toℕ-n+ {1} {d} {0} {SurjCond⇒IsSurj (WithZerosUnary d≥2)} n ∙) ⟩
        suc (n + zero)
    ≡⟨ cong suc (+-right-identity n) ⟩
        suc n
    ∎
toℕ-fromℕ             zero    | Surj (WithZeros b≥2 d≥b) = refl
toℕ-fromℕ {b} {d} {_} (suc n) | Surj (WithZeros b≥2 d≥b) =
    begin
        toℕ (1+ (n+ {b} {d} {0} n ∙))
    ≡⟨ toℕ-1+ {b} {d} {0} {SurjCond⇒IsSurj (WithZeros b≥2 d≥b)} (n+ n ∙) ⟩
        suc (toℕ (n+ n ∙))
    ≡⟨ cong suc (toℕ-n+ {b} {d} {0} {SurjCond⇒IsSurj (WithZeros b≥2 d≥b)} n ∙) ⟩
        suc (n + zero)
    ≡⟨ cong suc (+-right-identity n) ⟩
        suc n
    ∎
toℕ-fromℕ {b} {d} {_} zero    | Surj (Zeroless b≥1 d≥b) = refl
toℕ-fromℕ {b} {d} {_} (suc n) | Surj (Zeroless b≥1 d≥b) =
    begin
        toℕ (1+ (n+ {b} {d} {1} n ∙))
    ≡⟨ toℕ-1+ {b} {d} {1} {SurjCond⇒IsSurj (Zeroless b≥1 d≥b)} (n+ n ∙) ⟩
        suc (toℕ (n+ n ∙))
    ≡⟨ cong suc (toℕ-n+ {b} {d} {1} {SurjCond⇒IsSurj (Zeroless b≥1 d≥b)} n ∙) ⟩
        suc (n + zero)
    ≡⟨ cong suc (+-right-identity n) ⟩
        suc n
    ∎
toℕ-fromℕ {isSurjective = ()} n | NonSurj x


------------------------------------------------------------------------
-- Lemmata for proving Spurious cases not surjective
------------------------------------------------------------------------

lemma1 : ∀ {d o} → (xs : Num 0 d o) → toℕ xs ≢ suc (o + d)
lemma1 {d} {o} ∙        ()
lemma1 {d} {o} (x ∷ xs) p = contradiction p (<⇒≢ ⟦x∷xs⟧<1+o+d)
    where
        ⟦x∷xs⟧<1+o+d : o + Fin.toℕ x + toℕ xs * 0 < suc (o + d)
        ⟦x∷xs⟧<1+o+d = s≤s $
            start
                o + Fin.toℕ x + toℕ xs * zero
            ≤⟨ reflexive (cong (λ w → o + Fin.toℕ x + w) (*-right-zero (toℕ xs))) ⟩
                o + Fin.toℕ x + zero
            ≤⟨ reflexive (+-right-identity (o + Fin.toℕ x)) ⟩
                o + Fin.toℕ x
            ≤⟨ n+-mono o (
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
lemma4 (z ∷ xs) p = contradiction (
    begin
        toℕ xs
    ≡⟨ sym (*-right-identity (toℕ xs)) ⟩
        toℕ xs * 1
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
        ⟦x∷xs⟧>o+d : o + Fin.toℕ x + toℕ xs * b < o + d
        ⟦x∷xs⟧>o+d = start
                suc (o + Fin.toℕ x + toℕ xs * b)
            ≤⟨ reflexive (begin
                    suc (o + Fin.toℕ x + toℕ xs * b)
                ≡⟨ cong (λ w → suc (o + Fin.toℕ x + w * b)) ⟦xs⟧≡0 ⟩
                    suc (o + Fin.toℕ x + zero)
                ≡⟨ +-right-identity (suc (o + Fin.toℕ x)) ⟩
                    suc (o + Fin.toℕ x)
                ≡⟨ sym (+-suc o (Fin.toℕ x)) ⟩
                    o + suc (Fin.toℕ x)
                ∎) ⟩
                o + suc (Fin.toℕ x)
            ≤⟨ n+-mono o (bounded x) ⟩
                o + d
            □

lemma5 {b} {d} {o} d≥1 b≰d (x ∷ xs) p | no ¬q =
    contradiction p (>⇒≢ ⟦x∷xs⟧>o+d)
    where
        ⟦x∷xs⟧>o+d : o + Fin.toℕ x + toℕ xs * b > o + d
        ⟦x∷xs⟧>o+d = start
                suc (o + d)
            ≤⟨ reflexive (sym (+-suc o d)) ⟩
                o + suc d
            ≤⟨ n+-mono o (
                start
                    suc d
                ≤⟨ ≰⇒> b≰d ⟩
                    b
                ≤⟨ reflexive (sym (*-left-identity b)) ⟩
                    1 * b
                ≤⟨ _*-mono_ {1} {toℕ xs} {b} {b} (≰⇒> ¬q) ≤-refl ⟩
                    toℕ xs * b
                ≤⟨ n≤m+n (Fin.toℕ x) (toℕ xs * b) ⟩
                    Fin.toℕ x + toℕ xs * b
                □
            ) ⟩
                o + (Fin.toℕ x + toℕ xs * b)
            ≤⟨ reflexive (sym (+-assoc o (Fin.toℕ x) (toℕ xs * b))) ⟩
                o + Fin.toℕ x + toℕ xs * b
            □

NonSurjCond⇏Surjective : ∀ {b} {d} {o} → NonSurjCond b d o → ¬ (Surjective (Num⟶ℕ b d o))
NonSurjCond⇏Surjective {_} {d} {o} Base≡0              claim =
    lemma1 (from claim ⟨$⟩ suc o + d) (right-inverse-of claim (suc (o + d)))
NonSurjCond⇏Surjective NoDigits            claim =
    lemma2      (from claim ⟨$⟩ 1)    (right-inverse-of claim 1)
NonSurjCond⇏Surjective (Offset≥2 p)        claim =
    lemma3 p    (from claim ⟨$⟩ 1)    (right-inverse-of claim 1)
NonSurjCond⇏Surjective UnaryWithOnlyZeros     claim =
    lemma4     (from claim ⟨$⟩ 1)     (right-inverse-of claim 1)
NonSurjCond⇏Surjective {_} {d} {o} (NotEnoughDigits p q) claim =
    lemma5 p q (from claim ⟨$⟩ o + d) (right-inverse-of claim (o + d))

Surjective? : ∀ b d o → Dec (Surjective (Num⟶ℕ b d o))
Surjective? b d o with surjectionView b d o
Surjective? b d o | Surj cond = yes (record
    { from = ℕ⟶Num b d o
    ; right-inverse-of = toℕ-fromℕ {b} {d} {o} {SurjCond⇒IsSurj cond} })
Surjective? b d o | NonSurj reason = no (NonSurjCond⇏Surjective reason)
