module NumeralSystem where -- One Numeral System to rule them all!?

open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
open import Data.Product

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)


open import Function.Surjection using (Surjective)
open import Relation.Binary

open import Level
  renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; setoid)

open import Relation.Binary using (IsEquivalence)
open import Function.Equality using (_⟶_)

infixr 5 _∷[_,_]_

--  PN - Positional Notation
--  http://en.wikipedia.org/wiki/Positional_notation
--
--  base: b
--  digits: consecutive ℕ from m to n
--                             ●────○

data PN : (b m n : ℕ) → (m < n) → Set where
  [] : ∀ {b m n m<n} → PN b m n m<n
  _∷[_,_]_ : ∀ {b m n m<n} → (x : ℕ) → (x ≥ m) → (x < n)
    → PN b m n m<n → PN b m n m<n

trivial : ∀ {b m n m<n} → PN b m n m<n → Set
trivial {zero} _ = ⊤                        -- base: 0
trivial {suc b} {zero} {zero} {()}
trivial {suc b} {zero} {suc zero} x = ⊤     -- digits: {0}
trivial {suc b} {zero} {suc (suc n)} x = ⊥
trivial {suc b} {suc m} x = ⊥

surjective : ∀ {A B} → (A → B) → Set
surjective f = ∀ b → ∃ (λ a → f a ≡ b)

toℕ : ∀ {b m n m<n} → PN b m n m<n → ℕ
toℕ [] = 0
toℕ (x ∷[ x≥m , x<n ] xs) = x + toℕ xs

{-
incr : ∀ {b m n m<n m+b≤n} → (p : PN b m n m<n m+b≤n) → nonNil p → PN b m n m<n m+b≤n
incr [] ()
incr {b} {m} {n} {m<n} {m+b≤n} (x ∷[ x≥m , x<n ] xs) p with suc x ≟ b
... | yes q = m ∷[ {!   !} , {!   !} ] incr {!   !} {!   !}
... | no ¬q = (suc x) ∷[ {!   !} , {!   !} ] xs
-}

--
--  Instances
--

-- Unary
Unary : Set
Unary = PN 1 1 2 (s≤s (s≤s z≤n))

u₀ : Unary
u₀ = 1 ∷[ s≤s z≤n , s≤s (s≤s z≤n) ] 1 ∷[ s≤s z≤n , s≤s (s≤s z≤n) ] []

-- Binary
Bin : Set
Bin = PN 2 0 2 (s≤s z≤n)

b₀ : Bin
b₀ = 1 ∷[ z≤n , s≤s (s≤s z≤n) ] 0 ∷[ z≤n , s≤s z≤n ] []

-- Zeroless Binary
Bin+ : Set
Bin+ = PN 2 1 3 (s≤s (s≤s z≤n))


{-
incr : {b m n : ℕ} → (m < 2) → (n ≥ 2) → PositionalNotation b m n → PositionalNotation b m n
incr (s≤s m<2) n≥2 (Nil m<n m+b≤n) = Cons 1 m<n m+b≤n m<2 n≥2 (Nil m<n m+b≤n)
incr {b} {m} {n} (s≤s m<2) n≥2 (Cons x m<n m+b≤n x≥m x<n xs) with (n ≤? suc x)
... | yes p = Cons (suc x ∸ b) m<n m+b≤n {!   !} {!   !} (incr (s≤s m<2) n≥2 xs)
... | no ¬p = Cons (suc x) m<n m+b≤n {!   !} {!   !} xs

fromℕ : {b m n : ℕ} → (m < 2) → (n ≥ 2) → ℕ → PositionalNotation b m n
fromℕ (s≤s m≤1) n≥2 zero = Nil {!   !} {!   !}
fromℕ (s≤s m≤1) n≥2 (suc n) = incr (s≤s m≤1) n≥2 (fromℕ (s≤s m≤1) n≥2 n)


toℕ-surjective : Surjective (record { _⟨$⟩_ = toℕ ; cong = λ x → x })
toℕ-surjective = record { from = record { _⟨$⟩_ = fromℕ (s≤s z≤n) (s≤s (s≤s z≤n)) ; cong = λ x → x } ; right-inverse-of = λ x → x }
-}

-- PN-Setoid : {b m n : ℕ} → Setoid _ _
-- PN-Setoid {b} {m} {n} = setoid (PositionalNotation b m n)

-- ℕ-Setoid : Setoid _ _
-- ℕ-Setoid = setoid ℕ
