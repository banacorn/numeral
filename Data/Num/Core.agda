module Data.Num.Core where


open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Data.Fin.Properties using (bounded; toℕ-fromℕ≤)

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


------------------------------------------------------------------------
-- Digit
------------------------------------------------------------------------

Digit-toℕ : ∀ {d} → Digit d → ℕ → ℕ
Digit-toℕ d o = o + Fin.toℕ d


Digit-toℕ-fromℕ≤ : ∀ {d o n} → (p : n < d) → Digit-toℕ (fromℕ≤ p) o ≡ n + o
Digit-toℕ-fromℕ≤ {d} {o} {n} p =
    begin
        o + Fin.toℕ (fromℕ≤ p)
    ≡⟨ cong (_+_ o) (toℕ-fromℕ≤ p) ⟩
        o + n
    ≡⟨ +-comm o n ⟩
        n + o
    ∎

Digit<d+o : ∀ {d} → (x : Digit d) → (o : ℕ) → Digit-toℕ x o < d + o
Digit<d+o {d} x o =
    start
        suc (o + Fin.toℕ x)
    ≤⟨ reflexive (sym (+-suc o (Fin.toℕ x))) ⟩
        o + suc (Fin.toℕ x)
    ≤⟨ n+-mono o (bounded x) ⟩
        o + d
    ≤⟨ reflexive (+-comm o d) ⟩
        d + o
    □

-- A digit at its greatest
full : ∀ {d} (x : Fin d) → Dec (suc (Fin.toℕ x) ≡ d)
full {d} x = suc (Fin.toℕ x) ≟ d

-- +1 and then -base, useful for handling carrying on increment

digit+1-b-lemma : ∀ {b d}
    → (x : Digit d)
    → (redundant : suc b ≤ d)
    → (full : True (full x))
    → suc (Fin.toℕ x) ∸ suc b < d
digit+1-b-lemma {b} {d} x redundant full =
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
    → (full : True (full x))
    → Digit d
digit+1-b {b} {d} x redundant full
    = fromℕ≤ {suc (Fin.toℕ x) ∸ suc b} (digit+1-b-lemma x redundant full)

toℕ-digit-1-b : ∀ {b d}
    → (x : Digit d)
    → (redundant : suc b ≤ d)
    → (full : True (full x))
    → Fin.toℕ (digit+1-b x redundant full) ≡ suc (Fin.toℕ x) ∸ suc b
toℕ-digit-1-b {b} {d} x redundant full = toℕ-fromℕ≤ $ goal
    where   goal : suc (Fin.toℕ x ∸ b) ≤ d
            goal = {!   !}
    -- start
    --     {!   !}
    -- ≤⟨ {!   !} ⟩
    --     {!   !}
    -- ≤⟨ {!   !} ⟩
    --     {!   !}
    -- ≤⟨ {!   !} ⟩
    --     {!   !}
    -- □

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
