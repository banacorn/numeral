-- https://personal.cis.strath.ac.uk/conor.mcbride/PolyTest.pdf

module Sandbox.PolyTest where

open import Data.Nat
open import Data.Nat.Properties.Extra
open import Relation.Binary.PropositionalEquality

_^_ : ℕ → ℕ → ℕ
x ^ zero  = suc zero
x ^ suc y = x * (x ^ y)

-- data Poly : ℕ → Set where
--    κ : ℕ → Poly 0
--    ι : Poly 1
--    _⊕_ : ∀ {l m} → Poly l → Poly m → Poly (l ⊓ m)
--    _⊗_ : ∀ {l m} → Poly l → Poly m → Poly (l * m)
--
-- ⟦_⟧_ : ∀ {n} → Poly n → ℕ → ℕ
-- ⟦ κ c ⟧ x = c
-- ⟦ ι ⟧ x = x
-- ⟦ p ⊕ q ⟧ x = ⟦ p ⟧ x + ⟦ q ⟧ x
-- ⟦ p ⊗ q ⟧ x = ⟦ p ⟧ x * ⟦ q ⟧ x
--
-- Δ : ∀ {n} → Poly (suc n) → Poly n
-- Δ p = {! p  !}
-- -- I'm not sure if there should be a case for the constructor _⊕_,
-- -- because I get stuck when trying to solve the following unification
-- -- problems (inferred index ≟ expected index):
-- --   l ⊓ m ≟ suc n
-- -- when checking that the expression ? has type Poly .n


-- data Poly : ℕ → Set where
--    κ : ℕ → Poly 0
--    ι : Poly 1
--    plus : ∀ {l m n} → Poly l → Poly m → (l ⊓ m) ≡ n → Poly n
--    times : ∀ {l m n} → Poly l → Poly m → (l * m) ≡ n → Poly n
--
-- ⟦_⟧_ : ∀ {n} → Poly n → ℕ → ℕ
-- ⟦ κ c ⟧ x = c
-- ⟦ ι ⟧ x = x
-- ⟦ plus p q eq ⟧ x = ⟦ p ⟧ x + ⟦ q ⟧ x
-- ⟦ times p q eq ⟧ x = ⟦ p ⟧ x * ⟦ q ⟧ x

-- Δ : ∀ {n} → Poly (suc n) → Poly n
-- Δ ι = κ 1
-- Δ (plus (κ x) q ())
-- Δ (plus ι (κ x) ())
-- Δ (plus ι ι eq) = plus (Δ ι) (Δ ι) (cancel-suc eq)
-- Δ (plus ι (plus p₂ q₂ eq₂) eq) = plus (Δ ι) (Δ {! (plus p₂ q₂ eq₂)  !}) {!   !}
-- Δ (plus ι (times p₂ q₂ eq₂) eq) = {!   !}
-- -- Δ (plus ι q eq) = plus (Δ ι) (Δ {!   !}) {!   !}
-- Δ (plus (plus p q' eq') q eq) = {!   !}
-- Δ (plus (times p q' eq') q eq) = {!   !}
-- Δ (times p q eq) = {!   !}


-- data Poly : ℕ → Set where
--    κ     : ∀ {n}                                 → ℕ → Poly n
--    ι     : ∀ {n}                                      → Poly (suc n)
--    plus  : ∀ {n}     → Poly n → Poly n               → Poly n
--    times : ∀ {l m n} → Poly l → Poly m → (l * m) ≡ n → Poly n
--
-- -- ∆(p ⊗ r) = ∆p ⊗ (r · (1+)) ⊕ p ⊗ ∆r
-- Δ : ∀ {n} → Poly (suc n) → Poly n
-- Δ (κ x)          = κ 0
-- Δ ι              = κ 1
-- Δ (plus p q)     = plus (Δ p) (Δ q)
-- Δ (times p q eq) = times (Δ {! p  !}) {!   !} {!   !}

data Add : ℕ → ℕ → ℕ → Set where
    0+n : ∀ {n} → Add 0 n n
    n+0 : ∀ {n} → Add n 0 n
    m+n : ∀ {l m n} → Add l m n → Add (suc l) (suc m) (suc (suc n))

data Poly : ℕ → Set where
   κ     : ∀ {n}                                 → ℕ → Poly n
   ι     : ∀ {n}                                      → Poly (suc n)
   ↑     : ∀ {n}     → Poly n                        → Poly n
   _⊕_  : ∀ {n}     → Poly n → Poly n               → Poly n
   times : ∀ {l m n} → Poly l → Poly m → Add l m n → Poly n
infixl 5 _⊕_

⟦_⟧_ : ∀ {n} → Poly n → ℕ → ℕ
⟦ κ c ⟧ x = c
⟦ ι ⟧ x = x
⟦ ↑ p ⟧ x = ⟦ p ⟧ suc x
⟦ p ⊕ q ⟧ x = ⟦ p ⟧ x + ⟦ q ⟧ x
⟦ times p q add ⟧ x = ⟦ p ⟧ x * ⟦ q ⟧ x

sucl : ∀ {l m n} → Add l m n → Add (suc l) m (suc n)
sucl (0+n {zero})  = n+0
sucl (0+n {suc n}) = m+n 0+n
sucl (n+0 {zero})  = n+0
sucl (n+0 {suc n}) = n+0
sucl (m+n add)     = m+n (sucl add)

sucr : ∀ {l m n} → Add l m n → Add l (suc m) (suc n)
sucr 0+n           = 0+n
sucr (n+0 {zero})  = 0+n
sucr (n+0 {suc n}) = m+n n+0
sucr (m+n add)     = m+n (sucr add)

-- -- ∆(p ⊗ q) = (∆p ⊗ (q · (1+))) ⊕ (p ⊗ ∆q)
Δ : ∀ {n} → Poly (suc n) → Poly n
Δ (κ c) = κ 0
Δ ι = κ 1
Δ (↑ p) = ↑ (Δ p)
Δ (p ⊕ q) = Δ p ⊕ Δ q
Δ (times p q 0+n) = times (κ (⟦ p ⟧ 0)) (Δ q) 0+n
Δ (times p q n+0) = times (Δ p) (κ (⟦ q ⟧ 0)) n+0
Δ (times p q (m+n add)) = times (Δ p) (↑ q) (sucr add) ⊕ times p (Δ q) (sucl add)

add : ∀ l m → Add l m (l + m)
add zero m = 0+n
add (suc l) m = sucl (add l m)

_⊗_ : ∀ {l m} → Poly l → Poly m → Poly (l + m)
_⊗_ {l} {m} p q = times p q (add l m)
infixr 6 _⊗_

ι₁ : Poly 1
ι₁ = ι

κ₀ : ℕ → Poly 0
κ₀ c = κ c

_⊛_ : ∀ {m} → Poly m → (n : ℕ) → Poly (n * m)
p ⊛ zero = κ 1
p ⊛ suc n = {!   !}
