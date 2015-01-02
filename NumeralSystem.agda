module NumeralSystem where -- One Numeral System to rule them all!?

open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
open import Data.Product

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_ ; yes; no)

open import Relation.Binary

open import Level
  renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; setoid; cong)

open import Data.Nat.Properties using (≤-step)
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

infixr 5 _∷[_,_]_

--------------------------------------------------------------------------------
--  PN - Positional Notation
--  http://en.wikipedia.org/wiki/Positional_notation
--
--  base: b
--  digits: consecutive ℕ from m to n
--                             ●────○

data PN (b m n : ℕ) : Set where
  [_] : m < n → PN b m n
  _∷[_,_]_ : (x : ℕ) → (m ≤ x) → (x < n) → PN b m n → PN b m n


--------------------------------------------------------------------------------
toℕ : ∀ {b m n} → PN b m n → ℕ
toℕ [ _ ] = 0
toℕ {b} (x ∷[ x≥m , x<n ] xs) = x + b * toℕ xs

private
   ≤→< : ∀ {m n} → m ≤ n → ¬ (m ≡ n) → m < n
   ≤→< {n = zero} z≤n 0≠0 = ⊥-elim (0≠0 refl)
   ≤→< {n = suc n} z≤n neq = s≤s z≤n
   ≤→< (s≤s m≤n) 1+m≠1+n = s≤s (≤→< m≤n (λ m≡n → 1+m≠1+n (cong suc m≡n)))

--------------------------------------------------------------------------------
-- increment
-- the image of 'incr' is "continuous" if when
--    b = 1 ⇒ m ≥ 1, n ≥ 2m
--    b > 1 ⇒ m ≥ 0, n ≥ m + b, n ≥ 1 + mb

incr : ∀ {b m n} → m ≤ 1 → 2 ≤ n → PN b m n → PN b m n
incr m≤1 2≤n [ m<n ] = 1 ∷[ m≤1 , 2≤n ] [ m<n ]
incr {b} {m} {n} m≤1 2≤n (x ∷[ m≤x , x<n ] xs) with suc x ≟ n
incr {b} {m} m≤1 2≤n (x ∷[ m≤x , x<n ] xs) | no  1+x≠n = suc x ∷[ ≤-step m≤x , ≤→< x<n 1+x≠n ] xs
incr {b} {m} m≤1 2≤n (x ∷[ m≤x , x<n ] xs) | yes refl  = m ∷[ ≤-refl , s≤s m≤x ] incr m≤1 2≤n xs

base=1-incr : ∀ {m n} → 1 ≤ m → m * 2 ≤ n → PN 1 m n → PN 1 m n
base=1-incr {m} {n} 1≤m 2m≤n [ m<n ] = m ∷[ ≤-refl , m<n ] [ m<n ]
base=1-incr {m} {n} 1≤m 2m≤n (x ∷[ m≤x , x<n ] xs) with suc x ≟ n
base=1-incr {m} {n} 1≤m 2m≤n (x ∷[ m≤x , x<n ] xs) | no 1+x≠n = suc x ∷[ ≤-step m≤x , ≤→< x<n 1+x≠n ] xs
base=1-incr {m} 1≤m 2m≤n (x ∷[ m≤x , x<n ] xs) | yes refl = m ∷[ ≤-refl , s≤s m≤x ] base=1-incr 1≤m 2m≤n xs

base>1-incr : ∀ {b m n} → 1 < b → 0 ≤ m → m + b ≤ n → m * b + 1 ≤ n → PN b m n → PN b m n
base>1-incr {b} {m} {n} 1<b 0≤m m+b≤n mb+1≤n [ m<n ] = m ∷[ ≤-refl , m<n ] [ m<n ]
base>1-incr {b} {m} {n} 1<b 0≤m m+b≤n mb+1≤n (x ∷[ m≤x , x<n ] xs) with suc x ≟ n
base>1-incr {b} {m} {n} 1<b 0≤m m+b≤n mb+1≤n (x ∷[ m≤x , x<n ] xs) | no 1+x≠n = suc x ∷[ ≤-step m≤x , ≤→< x<n 1+x≠n ] xs
base>1-incr {b} {m} 1<b 0≤m m+b≤n mb+1≤n (x ∷[ m≤x , x<n ] xs) | yes refl = m ∷[ ≤-refl , s≤s m≤x ] base>1-incr 1<b 0≤m m+b≤n mb+1≤n xs

--
--   A ── incr ⟶ A'
--   |             |
--  toℕ           toℕ
--   ↓             ↓
--   n ── suc ⟶ suc n
--

-- first attempt :p
unary-toℕ-hom : (a : PN 1 1 2) → suc (toℕ a) ≡ toℕ (base=1-incr (s≤s z≤n) (s≤s (s≤s z≤n)) a)
unary-toℕ-hom [ m<n ] = refl
unary-toℕ-hom (zero ∷[ () , x<n ] xs)
unary-toℕ-hom (suc zero ∷[ m≤x , x<n ] xs) = cong suc {!   !}
unary-toℕ-hom (suc (suc x) ∷[ m≤x , s≤s (s≤s ()) ] xs)



--------------------------------------------------------------------------------
--  Instances


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
