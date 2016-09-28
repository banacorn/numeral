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

starting-digit : ∀ {b d o} → SurjCond b d o → Digit d
starting-digit (WithZerosUnary d≥2) = fromℕ≤ {1} d≥2
starting-digit (WithZeros b≥2 d≥b) = fromℕ≤ {1} (≤-trans b≥2 d≥b)
starting-digit (Zeroless b≥1 d≥b) = fromℕ≤ {0} (≤-trans b≥1 d≥b)


-- (incrementable n) if there exists some n' : Num b d o such that ⟦ n' ⟧ℕ ≡ suc ⟦ n ⟧ℕ
incrementable : ∀ {b d o} → Num b d o → Set
incrementable {b} {d} {o} xs = Σ[ xs' ∈ Num b d o ] toℕ xs' ≡ suc (toℕ xs)

-- when a system has no digits at all
incrementable-lemma-no-digits : ∀ {b o} → (xs : Num b 0 o) → ¬ (incrementable xs)
incrementable-lemma-no-digits ∙ (∙ , ())
incrementable-lemma-no-digits ∙ (() ∷ xs , p)
incrementable-lemma-no-digits (() ∷ xs)

Num-b-1-0⇒≡0 : ∀ {b} → (xs : Num b 1 0) → toℕ xs ≡ 0
Num-b-1-0⇒≡0     ∙           = refl
Num-b-1-0⇒≡0 {b} (z    ∷ xs) = cong (λ w → w * b) (Num-b-1-0⇒≡0 xs)
Num-b-1-0⇒≡0     (s () ∷ xs)

Num-0-d-o⇒<d+o : ∀ {d o} → (xs : Num 0 (suc d) o) → toℕ xs < suc d + o
Num-0-d-o⇒<d+o ∙ = s≤s z≤n
Num-0-d-o⇒<d+o {d} {o} (x ∷ xs) = s≤s $
    start
        Digit-toℕ x o + toℕ xs * zero
    ≤⟨ reflexive $ begin
            Digit-toℕ x o + toℕ xs * zero
        ≡⟨ cong (_+_ (Digit-toℕ x o)) (*-right-zero (toℕ xs)) ⟩
            Digit-toℕ x o + zero
        ≡⟨ +-right-identity (Digit-toℕ x o) ⟩
            Digit-toℕ x o
    ∎ ⟩
        Digit-toℕ x o
    ≤⟨ ≤-pred (Digit<d+o x o) ⟩
        d + o
    □

-- when a system has only the digit 0
Num-b-1-0⇒¬incrementable : ∀ {b} → (xs : Num b 1 0) → ¬ (incrementable xs)
Num-b-1-0⇒¬incrementable {b} xs (xs' , p) = contradiction (
    begin
        0
    ≡⟨ sym (Num-b-1-0⇒≡0 xs') ⟩
        toℕ xs'
    ≡⟨ p ⟩
        suc (toℕ xs)
    ≡⟨ cong suc (Num-b-1-0⇒≡0 xs) ⟩
        1
    ∎) (λ ())

incrementable-lemma-2 : ∀ {b d o} → ¬ (incrementable {b} {suc d} {suc (suc o)} ∙)
incrementable-lemma-2 (∙ , ())
incrementable-lemma-2 (x ∷ xs , ())

incrementable-lemma-3 : ∀ {d o}
    → (x : Digit (suc d)) → (xs : Num 0 (suc d) o)
    → suc (Fin.toℕ x) ≡ suc d
    → ¬ (incrementable (x ∷ xs))
incrementable-lemma-3 x xs p (∙ , ())
incrementable-lemma-3 {d} {o} x xs p (x' ∷ xs' , q) =
    let x'≡1+x : Fin.toℕ x' ≡ suc (Fin.toℕ x)
        x'≡1+x  = cancel-+-right o
                $ cancel-+-right 0
                $ begin
                        Fin.toℕ x' + o + zero
                    ≡⟨ cong (_+_ (Digit-toℕ x' o)) (sym (*-right-zero (toℕ xs'))) ⟩
                        Fin.toℕ x' + o + toℕ xs' * zero
                    ≡⟨ q ⟩
                        suc (Fin.toℕ x + o + toℕ xs * zero)
                    ≡⟨ cong (_+_ (suc (Digit-toℕ x o))) (*-right-zero (toℕ xs)) ⟩
                        suc (Fin.toℕ x + o + zero)
                    ∎
        x'≡1+d : Fin.toℕ x' ≡ suc d
        x'≡1+d =
            begin
                Fin.toℕ x'
            ≡⟨ x'≡1+x ⟩
                suc (Fin.toℕ x)
            ≡⟨ p ⟩
                suc d
            ∎
        x'≢1+d : Fin.toℕ x' ≢ suc d
        x'≢1+d = <⇒≢ (bounded x')
    in contradiction x'≡1+d x'≢1+d

incrementable-lemma-4 : ∀ {b d o}
    → (x : Digit (suc d))
    → (xs xs' : Num (suc b) (suc d) o)
    → toℕ xs' ≡ suc (toℕ xs)
    → (redundant : suc b ≤ suc d)
    → (greatest : Greatest x)
    → toℕ (digit+1-b {b} x redundant greatest ∷ xs') ≡ suc (toℕ (x ∷ xs))
incrementable-lemma-4 {b} {d} {o} x xs xs' p redundant greatest =
    begin
        toℕ (digit+1-b {b} x redundant greatest ∷ xs')
    ≡⟨ refl ⟩
        Digit-toℕ (digit+1-b {b} x redundant greatest) o + toℕ xs' * suc b
    -- fuse Digit-toℕ with digit+1-b
    ≡⟨ cong (λ w → w + toℕ xs' * suc b) (Digit-toℕ-digit+1-b x redundant greatest) ⟩
        Fin.toℕ x ∸ b + o + toℕ xs' * suc b
    -- p : toℕ xs' ≡ suc (toℕ xs)
    ≡⟨ cong (λ w → (Fin.toℕ x ∸ b) + o + w * suc b) p ⟩
    -- moving things around
        Fin.toℕ x ∸ b + o + suc (b + toℕ xs * suc b)
    ≡⟨ +-suc (Fin.toℕ x ∸ b + o) (b + toℕ xs * suc b) ⟩
        suc (Fin.toℕ x ∸ b + o + (b + toℕ xs * suc b))
    ≡⟨ sym (+-assoc (suc (Fin.toℕ x ∸ b + o)) b (toℕ xs * suc b)) ⟩
        suc (Fin.toℕ x ∸ b + o + b + toℕ xs * suc b)
    ≡⟨ cong (λ w → suc (w + toℕ xs * suc b)) ([a+b]+c≡[a+c]+b (Fin.toℕ x ∸ b) o b) ⟩
        suc (Fin.toℕ x ∸ b + b + o + toℕ xs * suc b)
    -- remove that annoying "∸ b + b"
    ≡⟨ cong (λ w → suc (w + o + toℕ xs * suc b)) (m∸n+n $ ≤-pred $
        start
            suc b
        ≤⟨ redundant ⟩
            suc d
        ≤⟨ reflexive (sym greatest) ⟩
            suc (Fin.toℕ x)
        □ ) ⟩
        suc (Fin.toℕ x + o + toℕ xs * suc b)
    ∎

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
tail-mono-strict : ∀ {b d o} (x y : Digit d) (xs ys : Num b d o)
    → Greatest x
    → toℕ (x ∷ xs) < toℕ (y ∷ ys)
    → toℕ xs < toℕ ys
tail-mono-strict {b} {_} {o} x y xs ys greatest p
    = *n-mono-strict-inverse b ⟦∷xs⟧<⟦∷ys⟧
    where
        ⟦x⟧≥⟦y⟧ : Digit-toℕ x o ≥ Digit-toℕ y o
        ⟦x⟧≥⟦y⟧ = greatest-of-all o x y greatest
        ⟦∷xs⟧<⟦∷ys⟧ : toℕ xs * b < toℕ ys * b
        ⟦∷xs⟧<⟦∷ys⟧ = +-mono-contra ⟦x⟧≥⟦y⟧ p

incrementable-lemma-5 : ∀ {b d o}
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → (¬redundant : suc b ≰ suc d)
    → Greatest x
    → incrementable (x ∷ xs)
    → ⊥
incrementable-lemma-5 x xs ¬redundant greatest (∙ , ())
incrementable-lemma-5 x ∙ ¬redundant greatest (y ∷ ∙ , claim) = {!   !}
incrementable-lemma-5 x ∙ ¬redundant greatest (y ∷ y' ∷ ys , claim) = {!   !}
incrementable-lemma-5 x (x' ∷ xs) ¬redundant greatest (y ∷ ∙ , claim) = {!   !}
incrementable-lemma-5 x (x' ∷ xs) ¬redundant greatest (y ∷ y' ∷ ys , claim) = {!   !}
    -- = contradiction 1+⟦x∷xs⟧≡⟦y∷ys⟧ (>⇒≢ 1+⟦x∷xs⟧<⟦y∷ys⟧)
    -- where   1+⟦x∷xs⟧<⟦y∷ys⟧ : suc (toℕ (x ∷ xs)) < toℕ (y ∷ ys)
    --         1+⟦x∷xs⟧<⟦y∷ys⟧ =
    --             start
    --                 suc (suc (o + Fin.toℕ x + toℕ xs * suc b))
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             □
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
incrementable? : ∀ {b d o} → (xs : Num b d o) → Dec (incrementable xs)
-- no digits at all
incrementable? {_} {zero}               xs = no (incrementable-lemma-no-digits xs)
-- all numbers evaluates to 0
incrementable? {_} {suc zero}    {zero} ∙  = no (Num-b-1-0⇒¬incrementable ∙)
incrementable? {_} {suc (suc d)} {zero} ∙  = yes ((fromℕ≤ {1} (s≤s (s≤s z≤n)) ∷ ∙) , refl)
incrementable? {d = suc d} {suc zero} ∙ = yes (z ∷ ∙ , refl)
-- digits starts from 2, impossible to increment from 0
incrementable? {d = suc d} {suc (suc o)} ∙ = no incrementable-lemma-2
-- see if the LSD is at its largest
incrementable? {d = suc d} (x ∷ xs) with Greatest? x
-- the system is bounded because base = 0
incrementable? {zero} {suc d} (x ∷ xs) | yes greatest = no (incrementable-lemma-3 x xs greatest)
incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest with incrementable? xs
incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | yes (xs' , q) with suc b ≤? suc d
incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | yes (xs' , q) | yes r
    = yes (digit+1-b {b} x r greatest ∷ xs' , incrementable-lemma-4 x xs xs' q r greatest)
incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | yes (xs' , q) | no ¬r
    = no (incrementable-lemma-5 x xs ¬r greatest)
incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | no ¬q = no {!   !}
incrementable? {b} {suc d} (x ∷ xs) | no ¬p = yes {!   !}



--
--
-- 1+ : ∀ {b d o} → Num b d o → Num b d o
-- 1+ {b} {d} {o} xs with surjectionView b d o
-- 1+ ∙        | Surj cond = starting-digit cond ∷ ∙
-- 1+ (x ∷ xs) | Surj cond with greatest x
-- 1+ (x ∷ xs) | Surj cond | yes p = digit+1-b-legacy x (SurjCond⇒b≥1 cond) p ∷ 1+ xs -- carry
-- 1+ (x ∷ xs) | Surj cond | no ¬p = digit+1   x ¬p                     ∷    xs
-- 1+ ∙        | NonSurj reason = ∙
-- 1+ (x ∷ xs) | NonSurj reason = xs
--
--
-- n+ : ∀ {b d o} → ℕ → Num b d o → Num b d o
-- n+ zero xs = xs
-- n+ (suc n) xs = 1+ (n+ n xs)
--
-- fromℕ : ∀ {b d o} → ℕ → Num b d o
-- fromℕ {b} {d} {o} n with surjectionView b d o
-- fromℕ n |    Surj x = n+ n ∙
-- fromℕ n | NonSurj x = ∙
--
--
-- -- fromℕ that preserves equality
-- ℕ⟶Num : ∀ b d o → setoid ℕ ⟶ setoid (Num b d o)
-- ℕ⟶Num b d o = record
--     { _⟨$⟩_ = fromℕ
--     ; cong = cong fromℕ
--     }
--
-- toℕ-digit+1-b : ∀ {d b} (x : Digit d)
--     → (b≥1 : b ≥ 1) → (p : suc (Fin.toℕ x) ≡ d)     -- required props
--     → Fin.toℕ (digit+1-b-legacy x b≥1 p) ≡ suc (Fin.toℕ x) ∸ b
-- toℕ-digit+1-b {d} {b} x b≥1 p = toℕ-fromℕ≤ $ start
--         suc (suc (Fin.toℕ x) ∸ b)
--     ≤⟨ s≤s (∸-mono ≤-refl b≥1) ⟩
--         suc (Fin.toℕ x)
--     ≤⟨ reflexive p ⟩
--         d
--     □
--
-- ------------------------------------------------------------------------
-- -- toℕ-1+ : toℕ (1+ xs) ≡ suc (toℕ xs)
-- ------------------------------------------------------------------------
--
-- toℕ-1+-x∷xs-greatest-lemma : ∀ {b d o}
--     → (x : Digit d) → (xs : Num b d o)
--     → (cond : SurjCond b d o)
--     → (p : suc (Fin.toℕ x) ≡ d)
--     → (toℕ-1+-xs : toℕ (1+ xs) ≡ suc (toℕ xs))
--     → toℕ (digit+1-b-legacy x (SurjCond⇒b≥1 cond) p ∷ 1+ xs) ≡ suc (toℕ (x ∷ xs))
-- toℕ-1+-x∷xs-greatest-lemma {b} {d} {o} x xs cond p toℕ-1+-xs =
--     begin
--         toℕ (digit+1-b-legacy x (SurjCond⇒b≥1 cond) p ∷ 1+ xs)
--     -- toℕ-fromℕ≤ : toℕ (fromℕ≤ m<n) ≡ m
--     ≡⟨ cong (λ w → o + w + toℕ (1+ xs) * b) (toℕ-fromℕ≤ ((digit+1-b-legacy-lemma x (SurjCond⇒b≥1 cond) p))) ⟩
--         o + (suc (Fin.toℕ x) ∸ b) + toℕ (1+ xs) * b
--     -- induction hypothesis
--     ≡⟨ cong (λ w → o + (suc (Fin.toℕ x) ∸ b) + w * b) toℕ-1+-xs ⟩
--         o + (suc (Fin.toℕ x) ∸ b) + (b + toℕ xs * b)
--     ≡⟨ +-assoc o (suc (Fin.toℕ x) ∸ b) (b + toℕ xs * b) ⟩
--         o + (suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b))
--     ≡⟨ cong (λ w → o + w) (sym (+-assoc (suc (Fin.toℕ x) ∸ b) b (toℕ xs * b))) ⟩
--         o + (suc (Fin.toℕ x) ∸ b + b + toℕ xs * b)
--     ≡⟨ cong (λ w → o + (w + toℕ xs * b)) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
--         o + (b + (suc (Fin.toℕ x) ∸ b) + toℕ xs * b)
--     -- m+n∸m≡n : m + (n ∸ m) ≡ n
--     ≡⟨ cong (λ w → o + (w + toℕ xs * b)) (m+n∸m≡n (
--             start
--                 b
--             ≤⟨ SurjCond⇒d≥b cond ⟩
--                 d
--             ≤⟨ reflexive (sym p) ⟩
--                 suc (Fin.toℕ x)
--             □)) ⟩
--         o + suc (Fin.toℕ x + toℕ xs * b)
--     ≡⟨ +-suc o (Fin.toℕ x + toℕ xs * b) ⟩
--         suc (o + (Fin.toℕ x + toℕ xs * b))
--     ≡⟨ cong suc (sym (+-assoc o (Fin.toℕ x) (toℕ xs * b))) ⟩
--         suc (o + Fin.toℕ x + toℕ xs * b)
--     ∎
--
-- toℕ-1+-x∷xs-not-greatest-lemma : ∀ {b d o}
--     → (x : Digit d) → (xs : Num b d o)
--     → (¬p : suc (Fin.toℕ x) ≢ d)
--     → toℕ (digit+1 x ¬p ∷ xs) ≡ suc (toℕ (x ∷ xs))
-- toℕ-1+-x∷xs-not-greatest-lemma {b} {d} {o} x xs ¬p =
--     begin
--         o + Fin.toℕ (fromℕ≤ (≤∧≢⇒< (bounded x) ¬p)) + toℕ xs * b
--     -- toℕ-fromℕ≤
--     ≡⟨ cong (λ w → o + w + toℕ xs * b) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p)) ⟩
--         o + suc (Fin.toℕ x) + toℕ xs * b
--     ≡⟨ +-assoc o (suc (Fin.toℕ x)) (toℕ xs * b) ⟩
--         o + suc (Fin.toℕ x + toℕ xs * b)
--     ≡⟨ +-suc o (Fin.toℕ x + toℕ xs * b) ⟩
--         suc (o + (Fin.toℕ x + toℕ xs * b))
--     ≡⟨ cong suc (sym (+-assoc o (Fin.toℕ x) (toℕ xs * b))) ⟩
--         suc (o + Fin.toℕ x + toℕ xs * b)
--     ∎
--
-- toℕ-1+ : ∀ {b d o}
--     → {isSurj : IsSurjective b d o}
--     → (xs : Num b d o)
--     → toℕ (1+ xs) ≡ suc (toℕ xs)
-- toℕ-1+ {b} {d} {o} xs with surjectionView b d o
-- toℕ-1+ {1} {d} {0} ∙ | Surj (WithZerosUnary d≥2) =
--     begin
--         Fin.toℕ (fromℕ≤ d≥2) + zero
--     ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ d≥2)) ⟩
--         Fin.toℕ (fromℕ≤ d≥2)
--     ≡⟨ toℕ-fromℕ≤ d≥2 ⟩
--         suc zero
--     ∎
-- toℕ-1+ {b} {d} {0} ∙ | Surj (WithZeros b≥2 d≥b) =
--     begin
--         Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b)) + zero * b
--     ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b))) ⟩
--         Fin.toℕ (fromℕ≤ (≤-trans b≥2 d≥b))
--     ≡⟨ toℕ-fromℕ≤ (≤-trans b≥2 d≥b) ⟩
--         suc zero
--     ∎
-- toℕ-1+ {b} {d} {_} ∙ | Surj (Zeroless b≥1 d≥b) =
--     begin
--         suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)) + zero)
--     ≡⟨ +-right-identity (suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)))) ⟩
--         suc (Fin.toℕ (fromℕ≤ (≤-trans b≥1 d≥b)))
--     ≡⟨ cong suc (toℕ-fromℕ≤ (≤-trans b≥1 d≥b)) ⟩
--         suc zero
--     ∎
-- toℕ-1+ {b} {d} {o} (x ∷ xs) | Surj condition with greatest x
-- toℕ-1+ {b} {d} {o} (x ∷ xs) | Surj condition | yes p = toℕ-1+-x∷xs-greatest-lemma x xs condition p (toℕ-1+ {isSurj = SurjCond⇒IsSurj condition} xs)
-- toℕ-1+ {b} {d} {o} (x ∷ xs) | Surj condition | no ¬p = toℕ-1+-x∷xs-not-greatest-lemma x xs ¬p
-- toℕ-1+ {isSurj = ()} xs | NonSurj reason
--
-- ------------------------------------------------------------------------
-- -- toℕ-n+ : toℕ (n+ n xs) ≡ n + (toℕ xs)
-- ------------------------------------------------------------------------
--
-- toℕ-n+ : ∀ {b d o}
--     → {isSurj : IsSurjective b d o}
--     → (n : ℕ)
--     → (xs : Num b d o)
--     → toℕ (n+ n xs) ≡ n + (toℕ xs)
-- toℕ-n+ {b} {d} {o} n xs with surjectionView b d o
-- toℕ-n+ zero xs | Surj cond = refl
-- toℕ-n+ (suc n) xs | Surj cond =
--     begin
--         toℕ (n+ (suc n) xs)
--     ≡⟨ refl ⟩
--         toℕ (1+ (n+ n xs))
--     ≡⟨ toℕ-1+ {isSurj = SurjCond⇒IsSurj cond} (n+ n xs) ⟩
--         suc (toℕ (n+ n xs))
--     ≡⟨ cong suc (toℕ-n+ {isSurj = SurjCond⇒IsSurj cond} n xs) ⟩
--         suc (n + toℕ xs)
--     ∎
-- toℕ-n+ {isSurj = ()} n xs | NonSurj reason
--
-- ------------------------------------------------------------------------
-- -- toℕ-fromℕ : toℕ (fromℕ n) ≡ n
-- ------------------------------------------------------------------------
--
-- toℕ-fromℕ : ∀ {b d o}
--     → {isSurjective : IsSurjective b d o}
--     → (n : ℕ)
--     → toℕ (fromℕ {b} {d} {o} n) ≡ n
-- toℕ-fromℕ {b} {d} {o} n       with surjectionView b d o
-- toℕ-fromℕ             zero    | Surj (WithZerosUnary d≥2) = refl
-- toℕ-fromℕ {_} {d} {_} (suc n) | Surj (WithZerosUnary d≥2) =
--     begin
--         toℕ (1+ (n+ {1} {d} {0} n ∙))
--     ≡⟨ toℕ-1+ {1} {d} {0} {SurjCond⇒IsSurj (WithZerosUnary d≥2)} (n+ n ∙) ⟩
--         suc (toℕ (n+ n ∙))
--     ≡⟨ cong suc (toℕ-n+ {1} {d} {0} {SurjCond⇒IsSurj (WithZerosUnary d≥2)} n ∙) ⟩
--         suc (n + zero)
--     ≡⟨ cong suc (+-right-identity n) ⟩
--         suc n
--     ∎
-- toℕ-fromℕ             zero    | Surj (WithZeros b≥2 d≥b) = refl
-- toℕ-fromℕ {b} {d} {_} (suc n) | Surj (WithZeros b≥2 d≥b) =
--     begin
--         toℕ (1+ (n+ {b} {d} {0} n ∙))
--     ≡⟨ toℕ-1+ {b} {d} {0} {SurjCond⇒IsSurj (WithZeros b≥2 d≥b)} (n+ n ∙) ⟩
--         suc (toℕ (n+ n ∙))
--     ≡⟨ cong suc (toℕ-n+ {b} {d} {0} {SurjCond⇒IsSurj (WithZeros b≥2 d≥b)} n ∙) ⟩
--         suc (n + zero)
--     ≡⟨ cong suc (+-right-identity n) ⟩
--         suc n
--     ∎
-- toℕ-fromℕ {b} {d} {_} zero    | Surj (Zeroless b≥1 d≥b) = refl
-- toℕ-fromℕ {b} {d} {_} (suc n) | Surj (Zeroless b≥1 d≥b) =
--     begin
--         toℕ (1+ (n+ {b} {d} {1} n ∙))
--     ≡⟨ toℕ-1+ {b} {d} {1} {SurjCond⇒IsSurj (Zeroless b≥1 d≥b)} (n+ n ∙) ⟩
--         suc (toℕ (n+ n ∙))
--     ≡⟨ cong suc (toℕ-n+ {b} {d} {1} {SurjCond⇒IsSurj (Zeroless b≥1 d≥b)} n ∙) ⟩
--         suc (n + zero)
--     ≡⟨ cong suc (+-right-identity n) ⟩
--         suc n
--     ∎
-- toℕ-fromℕ {isSurjective = ()} n | NonSurj x
--
--
-- ------------------------------------------------------------------------
-- -- Lemmata for proving Spurious cases not surjective
-- ------------------------------------------------------------------------
--
-- NonSurjCond-Base≡0 : ∀ {d o} → (xs : Num 0 d o) → toℕ xs ≢ suc (o + d)
-- NonSurjCond-Base≡0 {d} {o} ∙        ()
-- NonSurjCond-Base≡0 {d} {o} (x ∷ xs) p = contradiction p (<⇒≢ ⟦x∷xs⟧<1+o+d)
--     where
--         ⟦x∷xs⟧<1+o+d : o + Fin.toℕ x + toℕ xs * 0 < suc (o + d)
--         ⟦x∷xs⟧<1+o+d = s≤s $
--             start
--                 o + Fin.toℕ x + toℕ xs * zero
--             ≤⟨ reflexive (cong (λ w → o + Fin.toℕ x + w) (*-right-zero (toℕ xs))) ⟩
--                 o + Fin.toℕ x + zero
--             ≤⟨ reflexive (+-right-identity (o + Fin.toℕ x)) ⟩
--                 o + Fin.toℕ x
--             ≤⟨ n+-mono o (
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
-- NonSurjCond-NoDigits : ∀ {b o} → (xs : Num b 0 o) → toℕ xs ≢ 1
-- NonSurjCond-NoDigits ∙         ()
-- NonSurjCond-NoDigits (() ∷ xs)
--
-- NonSurjCond-Offset≥2 : ∀ {b d o} → o ≥ 2 → (xs : Num b d o) → toℕ xs ≢ 1
-- NonSurjCond-Offset≥2                   o≥2      ∙        ()
-- NonSurjCond-Offset≥2 {o = 0}           ()       (x ∷ xs) p
-- NonSurjCond-Offset≥2 {o = 1}           (s≤s ()) (x ∷ xs) p
-- NonSurjCond-Offset≥2 {o = suc (suc o)} o≥2      (x ∷ xs) ()
--
-- NonSurjCond-UnaryWithOnlyZeros : (xs : Num 1 1 0) → toℕ xs ≢ 1
-- NonSurjCond-UnaryWithOnlyZeros ∙ ()
-- NonSurjCond-UnaryWithOnlyZeros (z ∷ xs) p = contradiction (
--     begin
--         toℕ xs
--     ≡⟨ sym (*-right-identity (toℕ xs)) ⟩
--         toℕ xs * 1
--     ≡⟨ p ⟩
--         suc zero
--     ∎) (NonSurjCond-UnaryWithOnlyZeros xs)
-- NonSurjCond-UnaryWithOnlyZeros (s () ∷ xs)
--
-- NonSurjCond-NotEnoughDigits : ∀ {b d o} → d ≥ 1 → b ≰ d → (xs : Num b d o) → toℕ xs ≢ o + d
-- NonSurjCond-NotEnoughDigits {_} {_} {o} d≥1 b≰d ∙        = <⇒≢ (≤-steps o d≥1)
-- NonSurjCond-NotEnoughDigits {b} {d} {o} d≥1 b≰d (x ∷ xs) p with toℕ xs ≤? 0
-- NonSurjCond-NotEnoughDigits {b} {d} {o} d≥1 b≰d (x ∷ xs) p | yes q =
--     contradiction p (<⇒≢ ⟦x∷xs⟧>o+d)
--     where
--         ⟦xs⟧≡0 : toℕ xs ≡ 0
--         ⟦xs⟧≡0 = ≤0⇒≡0 (toℕ xs) q
--         ⟦x∷xs⟧>o+d : o + Fin.toℕ x + toℕ xs * b < o + d
--         ⟦x∷xs⟧>o+d = start
--                 suc (o + Fin.toℕ x + toℕ xs * b)
--             ≤⟨ reflexive (begin
--                     suc (o + Fin.toℕ x + toℕ xs * b)
--                 ≡⟨ cong (λ w → suc (o + Fin.toℕ x + w * b)) ⟦xs⟧≡0 ⟩
--                     suc (o + Fin.toℕ x + zero)
--                 ≡⟨ +-right-identity (suc (o + Fin.toℕ x)) ⟩
--                     suc (o + Fin.toℕ x)
--                 ≡⟨ sym (+-suc o (Fin.toℕ x)) ⟩
--                     o + suc (Fin.toℕ x)
--                 ∎) ⟩
--                 o + suc (Fin.toℕ x)
--             ≤⟨ n+-mono o (bounded x) ⟩
--                 o + d
--             □
--
-- NonSurjCond-NotEnoughDigits {b} {d} {o} d≥1 b≰d (x ∷ xs) p | no ¬q =
--     contradiction p (>⇒≢ ⟦x∷xs⟧>o+d)
--     where
--         ⟦x∷xs⟧>o+d : o + Fin.toℕ x + toℕ xs * b > o + d
--         ⟦x∷xs⟧>o+d = start
--                 suc (o + d)
--             ≤⟨ reflexive (sym (+-suc o d)) ⟩
--                 o + suc d
--             ≤⟨ n+-mono o (
--                 start
--                     suc d
--                 ≤⟨ ≰⇒> b≰d ⟩
--                     b
--                 ≤⟨ reflexive (sym (*-left-identity b)) ⟩
--                     1 * b
--                 ≤⟨ _*-mono_ {1} {toℕ xs} {b} {b} (≰⇒> ¬q) ≤-refl ⟩
--                     toℕ xs * b
--                 ≤⟨ n≤m+n (Fin.toℕ x) (toℕ xs * b) ⟩
--                     Fin.toℕ x + toℕ xs * b
--                 □
--             ) ⟩
--                 o + (Fin.toℕ x + toℕ xs * b)
--             ≤⟨ reflexive (sym (+-assoc o (Fin.toℕ x) (toℕ xs * b))) ⟩
--                 o + Fin.toℕ x + toℕ xs * b
--             □
--
-- NonSurjCond⇏Surjective : ∀ {b} {d} {o} → NonSurjCond b d o → ¬ (Surjective (Num⟶ℕ b d o))
-- NonSurjCond⇏Surjective {_} {d} {o} Base≡0  claim =
--     NonSurjCond-Base≡0
--         (from             claim ⟨$⟩ suc o + d)
--         (right-inverse-of claim   (suc (o + d)))
-- NonSurjCond⇏Surjective NoDigits claim =
--     NonSurjCond-NoDigits
--         (from             claim ⟨$⟩ 1)
--         (right-inverse-of claim     1)
-- NonSurjCond⇏Surjective (Offset≥2 p) claim =
--     NonSurjCond-Offset≥2 p
--         (from             claim ⟨$⟩ 1)
--         (right-inverse-of claim     1)
-- NonSurjCond⇏Surjective UnaryWithOnlyZeros claim =
--     NonSurjCond-UnaryWithOnlyZeros
--         (from             claim ⟨$⟩ 1)
--         (right-inverse-of claim     1)
-- NonSurjCond⇏Surjective {_} {d} {o} (NotEnoughDigits p q) claim =
--     NonSurjCond-NotEnoughDigits p q
--         (from             claim ⟨$⟩ o + d)
--         (right-inverse-of claim    (o + d))
--
-- SurjCond⇒Surjective : ∀ {b} {d} {o} → SurjCond b d o → Surjective (Num⟶ℕ b d o)
-- SurjCond⇒Surjective {b} {d} {o} cond = record
--     { from = ℕ⟶Num b d o
--     ; right-inverse-of = toℕ-fromℕ {b} {d} {o} {SurjCond⇒IsSurj cond}
--     }
--
-- Surjective? : ∀ b d o → Dec (Surjective (Num⟶ℕ b d o))
-- Surjective? b d o with surjectionView b d o
-- Surjective? b d o | Surj cond = yes (record
--     { from = ℕ⟶Num b d o
--     ; right-inverse-of = toℕ-fromℕ {b} {d} {o} {SurjCond⇒IsSurj cond}
--     })
-- Surjective? b d o | NonSurj reason = no (NonSurjCond⇏Surjective reason)
--
-- ------------------------------------------------------------------------
-- --
-- ------------------------------------------------------------------------
--
-- -- Surjective⇒SurjCond {b} {d} {o} surj = {!   !}
-- Surjective⇒SurjCond : ∀ {b} {d} {o}
--     → Surjective (Num⟶ℕ b d o)
--     → SurjCond b d o
-- Surjective⇒SurjCond {b} {d} {o} surj with surjectionView b d o
-- Surjective⇒SurjCond surj | Surj condition = condition
-- Surjective⇒SurjCond surj | NonSurj reason = contradiction surj (NonSurjCond⇏Surjective reason)
--
-- Surjective⇒IsSurj : ∀ {b} {d} {o} → Surjective (Num⟶ℕ b d o) → IsSurjective b d o
-- Surjective⇒IsSurj = SurjCond⇒IsSurj ∘ Surjective⇒SurjCond
--
-- Surjective⇒b≥1 : ∀ {b} {d} {o} → Surjective (Num⟶ℕ b d o) → b ≥ 1
-- Surjective⇒b≥1 = SurjCond⇒b≥1 ∘ Surjective⇒SurjCond
--
-- Surjective⇒d≥b : ∀ {b} {d} {o} → Surjective (Num⟶ℕ b d o) → b ≤ d
-- Surjective⇒d≥b = SurjCond⇒d≥b ∘ Surjective⇒SurjCond
