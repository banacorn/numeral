module Data.Num.Core where


open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Data.Fin.Properties as FinProps using (bounded; toℕ-fromℕ≤)

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Function.Equality using (_⟶_)

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)


-- For a system to be surjective with respect to ℕ:
-- * has zero
--     * base = 1 : {0, 1 ...}
--     * base = 2 : {0, 1 ...}
--     * base = 3 : {0, 1, 2 ...}
-- * zeroless
--     * base = 1 : {   1 ...}
--     * base = 2 : {   1, 2...}
--     * base = 3 : {   1, 2, 3...}

Digit : ℕ → Set
Digit = Fin

infixr 5 _∷_

data Num : ℕ → ℕ → ℕ → Set where
    ∙   : ∀ {b d o} → Num b d o
    _∷_ : ∀ {b d o} → Digit d → Num b d o → Num b d o


--------------------------------------------------------------------------------
-- Digit
--------------------------------------------------------------------------------

Digit-toℕ : ∀ {d} → Digit d → ℕ → ℕ
Digit-toℕ d o = Fin.toℕ d + o


Digit<d+o : ∀ {d} → (x : Digit d) → (o : ℕ) → Digit-toℕ x o < d + o
Digit<d+o {d} x o = +n-mono o (bounded x)

Greatest : ∀ {d} (x : Digit d) → Set
Greatest {d} x = suc (Fin.toℕ x) ≡ d

-- A digit at its greatest
Greatest? : ∀ {d} (x : Digit d) → Dec (Greatest x)
Greatest? {d} x = suc (Fin.toℕ x) ≟ d

greatest-digit : ∀ d → Digit (suc d)
greatest-digit d = Fin.fromℕ d

toℕ-greatest : ∀ {d o}
    → (x : Digit (suc d))
    → Greatest x
    → Digit-toℕ x o ≡ d + o
toℕ-greatest {d} {o} x greatest = suc-injective $ cong (λ w → w + o) greatest

greatest-of-all : ∀ {d} (o : ℕ) → (x y : Digit d) → Greatest x → Digit-toℕ x o ≥ Digit-toℕ y o
greatest-of-all o z     z      refl = ≤-refl
greatest-of-all o z     (s ()) refl
greatest-of-all o (s x) z      greatest = +n-mono o {zero} {suc (Fin.toℕ x)} z≤n
greatest-of-all o (s x) (s y)  greatest = s≤s (greatest-of-all o x y (suc-injective greatest))

greatest-digit-Greatest : ∀ d → Greatest (greatest-digit d)
greatest-digit-Greatest d = cong suc (FinProps.to-from d)

-- +1 and then -base, useful for handling carrying on increment


------------------------------------------------------------------------
-- Conversion to ℕ
------------------------------------------------------------------------



toℕ : ∀ {b d o} → Num b d o → ℕ
toℕ             ∙        = 0
toℕ {b} {_} {o} (x ∷ xs) = Digit-toℕ x o + toℕ xs * b

toℕ-Base≡0 : ∀ {d o}
    → (x : Digit d)
    → (xs : Num 0 d o)
    → toℕ (x ∷ xs) ≡ Digit-toℕ x o
toℕ-Base≡0 {d} {o} x xs =
    begin
        Digit-toℕ x o + toℕ xs * zero
    ≡⟨ cong (λ w → Digit-toℕ x o + w) (*-right-zero (toℕ xs)) ⟩
        Digit-toℕ x o + 0
    ≡⟨ +-right-identity (Digit-toℕ x o) ⟩
        Digit-toℕ x o
    ∎

∷ns-mono-strict : ∀ {b d o} (x y : Fin d) (xs ys : Num b d o)
    → toℕ xs ≡ toℕ ys
    → Digit-toℕ x o < Digit-toℕ y o
    → toℕ (x ∷ xs) < toℕ (y ∷ ys)
∷ns-mono-strict {b} {d} {o} x y xs ys ⟦xs⟧≡⟦ys⟧ ⟦x⟧<⟦y⟧ = start
        suc (Digit-toℕ x o + toℕ xs * b)
    ≈⟨ cong (λ w → suc (Digit-toℕ x o + w * b)) ⟦xs⟧≡⟦ys⟧ ⟩
        suc (Digit-toℕ x o + toℕ ys * b)
    ≤⟨ +n-mono (toℕ ys * b) ⟦x⟧<⟦y⟧ ⟩
        Digit-toℕ y o + toℕ ys * b
    □


------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

_≲_ : ∀ {b d o} → Num b d o → Num b d o → Set
xs ≲ ys = toℕ xs ≤ toℕ ys

-- _≋_ : ∀ {b d o} → Num b d o → Num b d o → Set
-- xs ≋ ys = toℕ xs ≡ toℕ ys

-- toℕ that preserves equality
Num⟶ℕ : ∀ b d o → setoid (Num b d o) ⟶ setoid ℕ
Num⟶ℕ b d o = record { _⟨$⟩_ = toℕ ; cong = cong toℕ }

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

-- _≋_ : ∀ {b d o}
--     → (xs ys : Num b d o)
--     → Dec ?
-- _≋_ {b}     {d}     {o} ∙        ∙        = yes = ?
--
-- _≋_ {b}     {d}     {o} ∙        (y ∷ ys) with Digit-toℕ y o ≟ 0
-- _≋_ {zero}  {d}     {o} ∙        (y ∷ ys) | yes p = ?
-- _≋_ {suc b} {d}         ∙        (y ∷ ys) | yes p = ?
-- _≋_ {b}     {d}         ∙        (y ∷ ys) | no ¬p = ?
--
-- _≋_ {b}     {d}     {o} (x ∷ xs) ∙        with Digit-toℕ x o ≟ 0
-- _≋_ {zero}              (x ∷ xs) ∙        | yes p = ?
-- _≋_ {suc b}             (x ∷ xs) ∙        | yes p = ?
-- _≋_ {b}     {d}     {o} (x ∷ xs) ∙        | no ¬p = ?
-- -- things get trickier here, we cannot say two numbers are equal or not base on
-- -- their LSD, since the system may be redundant.
-- _≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) with Digit-toℕ x o ≟ Digit-toℕ y o
-- _≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) | yes p = xs ≋ ys
-- _≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) | no ¬p = ⊥

Maximum : ∀ {b d o} → Num b d o → Set
Maximum {b} {d} {o} max = ∀ (xs : Num b d o) → toℕ max ≥ toℕ xs

-- a system is bounded if there exists the greatest number
Bounded : ∀ b d o → Set
Bounded b d o = Σ[ xs ∈ Num b d o ] Maximum xs

-- a system is Redundant if the number of digits is greater than the base
Redundant : ∀ b d → Set
Redundant b d = b < d

Redundant? : ∀ b d → Dec (Redundant b d)
Redundant? b d = suc b ≤? d

Digit-fromℕ : ∀ {d} → (n o : ℕ) → d + o ≥ n → Digit (suc d)
Digit-fromℕ {d} n o upper-bound with n ∸ o ≤? d
Digit-fromℕ {d} n o upper-bound | yes p = fromℕ≤ (s≤s p)
Digit-fromℕ {d} n o upper-bound | no ¬p = contradiction p ¬p
    where   p : n ∸ o ≤ d
            p = start
                    n ∸ o
                ≤⟨ ∸-mono {n} {d + o} {o} {o} upper-bound ≤-refl ⟩
                    (d + o) ∸ o
                ≤⟨ reflexive (m+n∸n≡m d o) ⟩
                    d
                □

Digit-toℕ-fromℕ : ∀ {d o}
    → (n : ℕ)
    → (upper-bound : d + o ≥ n)
    → (lower-bound :     o ≤ n)
    → Digit-toℕ (Digit-fromℕ {d} n o upper-bound) o ≡ n
Digit-toℕ-fromℕ {d} {o} n ub lb with n ∸ o ≤? d
Digit-toℕ-fromℕ {d} {o} n ub lb | yes q =
    begin
        Fin.toℕ (fromℕ≤ (s≤s q)) + o
    ≡⟨ cong (λ x → x + o) (toℕ-fromℕ≤ (s≤s q)) ⟩
        n ∸ o + o
    ≡⟨ m∸n+n lb ⟩
        n
    ∎
Digit-toℕ-fromℕ {d} {o} n ub lb | no ¬q = contradiction q ¬q
    where   q : n ∸ o ≤ d
            q = +n-mono-inverse o $
                start
                    n ∸ o + o
                ≤⟨ reflexive (m∸n+n lb) ⟩
                    n
                ≤⟨ ub ⟩
                    d + o
                □


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
Digit-toℕ-fromℕ≤ : ∀ {d o n} → (p : n < d) → Digit-toℕ (fromℕ≤ p) o ≡ n + o
Digit-toℕ-fromℕ≤ {d} {o} {n} p =
    begin
        Fin.toℕ (fromℕ≤ p) + o
    ≡⟨ cong (λ w → w + o) (toℕ-fromℕ≤ p) ⟩
        n + o
    ∎

digit+1-b-lemma : ∀ {d}
    → (x : Digit d)
    → (b : ℕ)
    → (b>0 : b > 0)
    → (redundant : Redundant b d)
    → Greatest x
    → suc (Fin.toℕ x) ∸ b < d
digit+1-b-lemma {_} x zero    ()  redundant greatest
digit+1-b-lemma {d} x (suc b) b>0 redundant greatest =
    start
        suc (suc (Fin.toℕ x) ∸ suc b)
    ≤⟨ s≤s (∸-mono {suc (Fin.toℕ x)} {d} {suc b} (bounded x) ≤-refl) ⟩
        suc (d ∸ suc b)
    ≤⟨ reflexive (sym (+-∸-assoc 1 {d} {suc b} (≤-pred (≤-step redundant)))) ⟩
        suc d ∸ suc b
    ≤⟨ reflexive ([i+j]∸[i+k]≡j∸k 1 d b) ⟩
        d ∸ b
    ≤⟨ ∸-mono {d} {d} {b} ≤-refl z≤n ⟩
        d
    □

digit+1 : ∀ {d} → (x : Digit d) → (¬p : suc (Fin.toℕ x) ≢ d) → Fin d
digit+1 x ¬p = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p)

Digit-toℕ-digit+1 : ∀ {d o}
    → (x : Digit d)
    → (¬p : suc (Fin.toℕ x) ≢ d)
    → Digit-toℕ (digit+1 x ¬p) o ≡ suc (Digit-toℕ x o)
Digit-toℕ-digit+1 {d} {o} x ¬p = cong (λ w → w + o) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p))

digit+1-b : ∀ {d}
    → (x : Digit d)
    → (b : ℕ)
    → (b>0 : b > 0)
    → (redundant : suc b ≤ d)
    → Greatest x
    → Digit d
digit+1-b {d} x b b>0 redundant greatest
    = fromℕ≤ {suc (Fin.toℕ x) ∸ b} (digit+1-b-lemma x b b>0 redundant greatest) -- (digit+1-b-lemma x redundant greatest)

Digit-toℕ-digit+1-b : ∀ {d o}
    → (x : Digit d)
    → (b : ℕ)
    → (b>0 : b > 0)
    → (redundant : suc b ≤ d)
    → (greatest : Greatest x)
    → Digit-toℕ {d} (digit+1-b {d} x b b>0 redundant greatest) o ≡ suc (Digit-toℕ x o) ∸ b
Digit-toℕ-digit+1-b {d} {o} x b b>0 redundant greatest =
    begin
        Fin.toℕ (fromℕ≤ (digit+1-b-lemma x b b>0 redundant greatest)) + o
    ≡⟨ cong (λ w → w + o) (toℕ-fromℕ≤ (digit+1-b-lemma x b b>0 redundant greatest)) ⟩
        (suc (Fin.toℕ x) ∸ b) + o
    ≡⟨ +-comm (suc (Fin.toℕ x) ∸ b) o ⟩
        o + (suc (Fin.toℕ x) ∸ b)
    ≡⟨ sym (+-∸-assoc o {suc (Fin.toℕ x)} {b} $
        start
            b
        ≤⟨ m≤n+m b (suc zero) ⟩
            suc b
        ≤⟨ redundant ⟩
            d
        ≤⟨ reflexive (sym greatest) ⟩
            suc (Fin.toℕ x)
        □)
    ⟩
        (o + suc (Fin.toℕ x)) ∸ b
    ≡⟨ cong (λ w → w ∸ b) (+-comm o (suc (Fin.toℕ x))) ⟩
        suc (Fin.toℕ x) + o ∸ b
    ∎
