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


Digit-toℕ-fromℕ≤ : ∀ {d o n} → (p : n < d) → Digit-toℕ (fromℕ≤ p) o ≡ n + o
Digit-toℕ-fromℕ≤ {d} {o} {n} p =
    begin
        Fin.toℕ (fromℕ≤ p) + o
    ≡⟨ cong (λ w → w + o) (toℕ-fromℕ≤ p) ⟩
        n + o
    ∎

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

digit+1-b-lemma : ∀ {b d}
    → (x : Digit d)
    → (redundant : suc b ≤ d)
    → Greatest x
    → suc (Fin.toℕ x) ∸ suc b < d
digit+1-b-lemma {b} {d} x redundant greatest =
    start
        suc (suc (Fin.toℕ x) ∸ suc b)
    ≤⟨ s≤s (∸-mono {suc (Fin.toℕ x)} {d} {suc b} {suc b} (bounded x) ≤-refl) ⟩
        suc (d ∸ suc b)
    ≤⟨ reflexive (sym (+-∸-assoc (suc zero) redundant)) ⟩
        suc d ∸ suc b
    ≤⟨ reflexive ([i+j]∸[i+k]≡j∸k 1 d b) ⟩
        d ∸ b
    ≤⟨ ∸-mono {d} {d} {b} ≤-refl z≤n ⟩
        d
    □

digit+1-b : ∀ {b d}
    → (x : Digit d)
    → (redundant : suc b ≤ d)
    → Greatest x
    → Digit d
digit+1-b {b} {d} x redundant greatest
    = fromℕ≤ {suc (Fin.toℕ x) ∸ suc b} (digit+1-b-lemma x redundant greatest)

toℕ-digit+1-b : ∀ {b d}
    → (x : Digit d)
    → (redundant : suc b ≤ d)
    → (greatest : Greatest x)
    → Fin.toℕ (digit+1-b x redundant greatest) ≡ suc (Fin.toℕ x) ∸ suc b
toℕ-digit+1-b {b} {d} x redundant greatest =
    begin
        Fin.toℕ (digit+1-b x redundant greatest)
    ≡⟨ refl ⟩
        Fin.toℕ (fromℕ≤  {suc (Fin.toℕ x) ∸ suc b} (digit+1-b-lemma x redundant greatest))
    ≡⟨ toℕ-fromℕ≤ (digit+1-b-lemma x redundant greatest) ⟩
        Fin.toℕ x ∸ b
    ≡⟨ sym ([i+j]∸[i+k]≡j∸k 1 (Fin.toℕ x) b) ⟩
        suc (Fin.toℕ x) ∸ suc b
    ∎

Digit-toℕ-digit+1-b : ∀ {b d o}
    → (x : Digit d)
    → (redundant : suc b ≤ d)
    → (greatest : Greatest x)
    → Digit-toℕ (digit+1-b x redundant greatest) o ≡ (suc (Fin.toℕ x) ∸ suc b) + o
Digit-toℕ-digit+1-b {b} {d} {o} x redundant greatest = cong (λ w → w + o) (toℕ-digit+1-b x redundant greatest)

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

digit+1-b-legacy-lemma : ∀ {b d} → (x : Digit d)
    → b ≥ 1 → suc (Fin.toℕ x) ≡ d
    → suc (Fin.toℕ x) ∸ b < d
digit+1-b-legacy-lemma {b} {d} x b≥1 p =
    start
        suc (suc (Fin.toℕ x) ∸ b)
    ≤⟨ s≤s (∸-mono ≤-refl b≥1) ⟩
        suc (Fin.toℕ x)
    ≤⟨ reflexive p ⟩
        d
    □

digit+1-b-legacy : ∀ {b d} → (x : Digit d) → b ≥ 1 → suc (Fin.toℕ x) ≡ d → Fin d
digit+1-b-legacy {b} {d} x b≥1 p = fromℕ≤ {suc (Fin.toℕ x) ∸ b} (digit+1-b-legacy-lemma x b≥1 p)

digit+1 : ∀ {d} → (x : Digit d) → (¬p : suc (Fin.toℕ x) ≢ d) → Fin d
digit+1 x ¬p = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p)



------------------------------------------------------------------------
-- Conversion to ℕ
------------------------------------------------------------------------



toℕ : ∀ {b d o} → Num b d o → ℕ
toℕ             ∙        = 0
toℕ {b} {_} {o} (x ∷ xs) = Digit-toℕ x o + toℕ xs * b


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

Suprenum : ∀ {b d o} → Num b d o → Set
Suprenum {b} {d} {o} sup = ∀ (xs : Num b d o) → toℕ sup ≥ toℕ xs

-- a system is bounded if there exists the greatest number
Bounded : ∀ b d o → Set
Bounded b d o = Σ[ xs ∈ Num b d o ] Suprenum xs
