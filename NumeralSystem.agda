module NumeralSystem where -- One Numeral System to rule them all!?

open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
-- open import Data.Unit using (⊤)
open import Relation.Nullary using (yes; no)


open import Function.Surjection using (Surjective)
open import Relation.Binary

open import Level
  renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; setoid)
open import Relation.Binary using (IsEquivalence)
open import Function.Equality using (_⟶_)
--
--  Type
--

--  Positional Notation
--  http://en.wikipedia.org/wiki/Positional_notation
--
--  digits range from m to n: [m, n)
data PositionalNotation : (base m n : ℕ) → Set where
  [] : {b m n : ℕ} → (m < n) → (m + b ≤ n) → PositionalNotation b m n
  ∷ : {b m n : ℕ} → (x : ℕ) → (m < n) → (m + b ≤ n) → (x ≥ m) → (x < n) → PositionalNotation b m n → PositionalNotation b m n

toℕ : {b m n : ℕ} → PositionalNotation b m n → ℕ
toℕ ([] m<n m+b≤n) = 0
toℕ (∷ x m<n m+b≤n x≥m x<n xs) = x + toℕ xs

incr : {b m n : ℕ} → (m < 2) → (n ≥ 2) → PositionalNotation b m n → PositionalNotation b m n
incr (s≤s m<2) n≥2 ([] m<n m+b≤n) = ∷ 1 m<n m+b≤n m<2 n≥2 ([] m<n m+b≤n)
incr {b} {m} {n} (s≤s m<2) n≥2 (∷ x m<n m+b≤n x≥m x<n xs) with (n ≤? suc x)
...                                                 | yes p = ∷ (suc x ∸ b) m<n m+b≤n {!   !} {!   !} (incr (s≤s m<2) n≥2 xs)
...                                                 | no ¬p = ∷ (suc x) m<n m+b≤n {!   !} {!   !} xs

fromℕ : {b m n : ℕ} → (m < 2) → (n ≥ 2) → ℕ → PositionalNotation b m n
fromℕ (s≤s m≤1) n≥2 zero = [] {!   !} {!   !}
fromℕ (s≤s m≤1) n≥2 (suc n) = incr (s≤s m≤1) n≥2 (fromℕ (s≤s m≤1) n≥2 n)


toℕ-surjective : Surjective (record { _⟨$⟩_ = toℕ ; cong = λ x → x })
toℕ-surjective = record { from = record { _⟨$⟩_ = fromℕ (s≤s z≤n) (s≤s (s≤s z≤n)) ; cong = λ x → x } ; right-inverse-of = λ x → x }


-- PN-Setoid : {b m n : ℕ} → Setoid _ _
-- PN-Setoid {b} {m} {n} = setoid (PositionalNotation b m n)

-- ℕ-Setoid : Setoid _ _
-- ℕ-Setoid = setoid ℕ


--
--  Instances
--

-- Unary
Unary : Set
Unary = PositionalNotation 1 1 2

-- Binary
Bin : Set
Bin = PositionalNotation 2 0 2

-- Zeroless Binary
Bin+ : Set
Bin+ = PositionalNotation 2 1 3
