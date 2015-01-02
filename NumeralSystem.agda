module NumeralSystem where -- One Numeral System to rule them all!?

open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
open import Data.Product

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_ ; yes; no)


open import Function.Surjection using (Surjective)
open import Relation.Binary

open import Level
  renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; setoid; cong)

open import Relation.Binary using (IsEquivalence)
open import Function.Equality using (_⟶_)

open import Data.Nat.Properties using (≤-step)
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

infixr 5 _∷[_,_]_

--  PN - Positional Notation
--  http://en.wikipedia.org/wiki/Positional_notation
--
--  base: b
--  digits: consecutive ℕ from m to n
--                             ●────○

data PN (b m n : ℕ) : Set where
  [_] : m < n → PN b m n
  _∷[_,_]_ : (x : ℕ) → (m ≤ x) → (x < n) → PN b m n → PN b m n 

{- What is this for? 
trivial : ∀ {b m n m<n} → PN b m n m<n → Set
trivial {zero} _ = ⊤                        -- base: 0
trivial {suc b} {zero} {zero} {()}
trivial {suc b} {zero} {suc zero} x = ⊤     -- digits: {0}
trivial {suc b} {zero} {suc (suc n)} x = ⊥
trivial {suc b} {suc m} x = ⊥
-}

surjective : ∀ {A B} → (A → B) → Set
surjective f = ∀ b → ∃ (λ a → f a ≡ b)

toℕ : ∀ {b m n} → PN b m n → ℕ
toℕ [ _ ] = 0
toℕ {b} (x ∷[ x≥m , x<n ] xs) = x + b * toℕ xs

private
   ≤→< : ∀ {m n} → m ≤ n → ¬ (m ≡ n) → m < n
   ≤→< {n = zero} z≤n 0≠0 = ⊥-elim (0≠0 refl)
   ≤→< {n = suc n} z≤n neq = s≤s z≤n
   ≤→< (s≤s m≤n) 1+m≠1+n = s≤s (≤→< m≤n (λ m≡n → 1+m≠1+n (cong suc m≡n)))

incr : ∀ {b m n} → m ≤ 1 → 2 ≤ n → PN b m n → PN b m n
incr m≤1 2≤n [ m<n ] = 1 ∷[ m≤1 , 2≤n ] [ m<n ]
incr {b} {m} {n} m≤1 2≤n (x ∷[ m≤x , x<n ] xs) with suc x ≟ n 
incr {b} {m} m≤1 2≤n (x ∷[ m≤x , x<n ] xs) | no  1+x≠n = suc x ∷[ ≤-step m≤x , ≤→< x<n 1+x≠n ] xs
incr {b} {m} m≤1 2≤n (x ∷[ m≤x , x<n ] xs) | yes refl  = m ∷[ ≤-refl , s≤s m≤x ] incr m≤1 2≤n xs

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
Unary = PN 1 1 2

u₀ : Unary
u₀ = 1 ∷[ s≤s z≤n , s≤s (s≤s z≤n) ] 1 ∷[ s≤s z≤n , s≤s (s≤s z≤n) ] [ s≤s (s≤s z≤n) ]

-- Binary
Bin : Set
Bin = PN 2 0 2 

b₀ : Bin
b₀ = 1 ∷[ z≤n , s≤s (s≤s z≤n) ] 0 ∷[ z≤n , s≤s z≤n ] [ s≤s z≤n ]

-- Zeroless Binary
Bin+ : Set
Bin+ = PN 2 1 3


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
