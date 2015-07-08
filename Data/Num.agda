
module Data.Num where

open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat
open ≤-Reasoning

open import Data.Nat.Etc
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Properties using (div-mono)
open import Data.Nat.Properties using (m≤m+n; n≤m+n;_+-mono_; pred-mono; ∸-mono; ≰⇒>; n∸n≡0; +-∸-assoc; m+n∸n≡m)
open import Data.Nat.Properties.Simple using (+-right-identity; +-suc; +-assoc; +-comm; distribʳ-*-+)
open import Data.Fin.Properties using (bounded)
open import Data.Fin using (Fin; fromℕ≤; inject≤; #_)
    renaming (toℕ to F→N; fromℕ to N→F; zero to Fz; suc to Fs)
open import Data.Product
open import Data.Maybe

open import Induction.Nat using (rec; Rec)
import Level
open import Function
open import Data.Unit using (tt)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse; fromWitness; fromWitnessFalse)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary

open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; sym; trans; inspect)
open PropEq.≡-Reasoning
    renaming (begin_ to beginEq_; _≡⟨_⟩_ to _≡Eq⟨_⟩_; _∎ to _∎Eq)
-- Surjective (ℕm):
--  base = 1, digits = {m ... (m + n) - 1}, m ≥ 1, n ≥ m
--  base > 1, digits = {m ... (m + n) - 1}, m ≥ 0, n ≥ max base (base × m)
-- Bijective:
--  base ≥ 1, digits = {1 .. base}
--
--  Digits:
--    Digit m n represents a Digit ranging from m to (m + n - 1)
--    e.g. Digit 2 0 2 = {0, 1}         for ordinary binary number
--         Digit 2 1 2 = {1, 2}         for zeroless binary number
--         Digit 2 0 3 = {0, 1, 2}      for redundant binary number
--
data Digit : (base from range : ℕ) → Set where
    -- unary digit: {0, 1 .. n-1}
    U0 : ∀ {n} → Fin n
         → {2≤n : True (2 ≤? n)} -- i.e. must have digit '1'
         → Digit 1 0 n
    -- unary digit: {m .. m+n-1}
    U1 : ∀ {m n}
         → Fin n
         → {m≤n : True (suc m ≤? n)}
         → Digit 1 (suc m) n
    -- k-adic digit: {m .. m+n-1}
    D  : ∀ {b m n}
         → Fin n
         → let base = suc (suc b) in
           {b≤n : True (base ≤? n)} → {bm≤n : True ((base * m) ≤? n)}
         → Digit base m n

-- without offset, {0 .. n-1}
D→F : ∀ {b m n} → Digit b m n → Fin n
D→F (U0 x) = x
D→F (U1 x) = x
D→F (D x) = x

-- with offset, {m .. m+n-1}
D→N : ∀ {b m n} → Digit b m n → ℕ
D→N {m = m} d = m + F→N (D→F d)

-- infix 4 _D≤_ -- _D<_ _≥′_ _>′_

-- data _D≤_ {b m n} (x : Digit b m n) : (y : Digit b m n) → Set where
--   D≤-refl :                          x D≤ x
--  D≤-step : ∀ {y} (xD≤y : x D≤ y) → x D≤
  -- ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n

private

    -- alias
    ℕ-isDecTotalOrder   = DecTotalOrder.isDecTotalOrder decTotalOrder
    ℕ-isTotalOrder      = IsDecTotalOrder.isTotalOrder ℕ-isDecTotalOrder
    ℕ-isPartialOrder    = IsTotalOrder.isPartialOrder ℕ-isTotalOrder
    ℕ-isPreorder        = IsPartialOrder.isPreorder ℕ-isPartialOrder
    ≤-refl      = IsPreorder.reflexive ℕ-isPreorder
    ≤-antisym   = IsPartialOrder.antisym ℕ-isPartialOrder
    ≤-total     = IsTotalOrder.total ℕ-isTotalOrder

    -- helper function for adding two 'Fin n' with offset 'm'
    -- (m + x) + (m + y) - m = m + x + y
    D+sum : ∀ {n} (m : ℕ) → (x y : Fin n) → ℕ
    D+sum m x y = m + (F→N x) + (F→N y)


suppress-pred : ℕ → Set
suppress-pred _ = ℕ → ℕ

suppress-rec-struct : (x : ℕ) → Rec Level.zero suppress-pred x → (bound : ℕ) → ℕ
suppress-rec-struct zero p bound = 0
suppress-rec-struct (suc x) p bound with bound ≤? suc (p bound)
suppress-rec-struct (suc x) p bound | yes q = suc (p bound) ∸ bound
suppress-rec-struct (suc x) p bound | no ¬q = suc (p bound)

-- if x ≥ bound, then substract bound from x, until x < bound
suppress : (x bound : ℕ) → ℕ
suppress = rec suppress-pred suppress-rec-struct

suppressed<bound : (x bound : ℕ) → (≢0 : False (bound ≟ 0)) → suppress x bound < bound
suppressed<bound zero    zero        ()
suppressed<bound zero    (suc bound) ≢0 = s≤s z≤n
suppressed<bound (suc x) zero        ()
suppressed<bound (suc x) (suc bound) ≢0 with suc bound ≤? suc (suppress x (suc bound))
suppressed<bound (suc x) (suc bound) ≢0 | yes p =
    begin
        suc (suppress x (suc bound) ∸ bound)
    ≤⟨ ≤-refl (sym (+-∸-assoc 1 p)) ⟩
        suc (suppress x (suc bound)) ∸ bound
    ≤⟨ ∸-mono {suc (suppress x (suc bound))} {suc bound} {bound} {bound} (suppressed<bound x (suc bound) tt) (≤-refl refl) ⟩
        suc bound ∸ bound
    ≤⟨ ≤-refl (m+n∸n≡m 1 bound) ⟩
        suc zero
    ≤⟨ s≤s z≤n ⟩
        suc bound
    ∎
suppressed<bound (suc x) (suc bound) ≢0 | no ¬p = ≰⇒> ¬p

suppress′ : (x bound : ℕ) → (≢0 : False (bound ≟ 0)) → Fin bound
suppress′ x bound ≢0 = fromℕ≤ {suppress x bound} (suppressed<bound x bound ≢0)

_D+_ : ∀ {b m n} → Digit b m n → Digit b m n → Digit b m n
_D+_ {zero}                ()     ()
_D+_ {suc zero}            x      _      = x
_D+_ {suc (suc b)} {m} {n} (D x) (D y {b≤n} {bm≤n}) = D (suppress′ (D+sum m x y) n n≢0) {b≤n} {bm≤n}
    where   n≢0 = fromWitnessFalse $ >⇒≢ $
                begin
                    suc zero
                ≤⟨ s≤s z≤n ⟩
                    suc (suc b)
                ≤⟨ toWitness b≤n ⟩
                    n
                ∎

--      2 ≤ base
--  ⇒  max * 2 ≤ max * base
--  ⇒  max * 2 / base ≤ max

{-
_D⊕_ : ∀ {b m n} → Digit b m n → Digit b m n → Maybe (Digit b m n)
_D⊕_                       (U0 x) y = just y
_D⊕_                       (U1 x) y = just y
_D⊕_ {suc (suc b)} {m} {n} (D x) (D y) with suc (D+sum m x y) ≤? n
_D⊕_ {suc (suc b)} {m} {n} (D x) (D y) | yes p = nothing
_D⊕_ {suc (suc b)} {m} {n} (D x) (D y {b≤n} {bm≤n}) | no ¬p with D+sum m x y divMod (suc (suc b)) | inspect (λ w → _divMod_ (D+sum m x y) (suc (suc b)) {≢0 = w}) tt
_D⊕_ {suc (suc b)} {m} {n} (D x) (D y {b≤n} {bm≤n}) | no ¬p | result quotient remainder property | PropEq.[ eq ] =
    let base = suc (suc b)
        sum = D+sum m x y
        quotient<n = begin
                suc quotient
            ≤⟨ div-mono base tt {!    !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                n
            ∎
    in  just (D (fromℕ≤ {quotient} quotient<n) {b≤n} {bm≤n})
-}
{-
    let base = suc (suc b)
        sum = D+sum m x y
        result quotient remainder property = _divMod_ sum base {tt}
        quotient<n = begin
                DivMod.quotient (sum divMod {! base  !})
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                n
            ∎
    in  just (D (fromℕ≤ {quotient} quotient<n) {b≤n} {bm≤n})
-}
{-


    begin
        {!   !}
    <⟨ {!   !} ⟩
        {!   !}
    <⟨ {!   !} ⟩
        {!   !}
    ∎

    begin
        {!   !}
    ≤⟨ {!    !} ⟩
        {!    !}
    ≤⟨ {!    !} ⟩
        {!   !}
    ≤⟨ {!    !} ⟩
        {!   !}
    ≤⟨ {!    !} ⟩
        {!   !}
    ∎
    beginEq
        {!   !}
    ≡Eq⟨ {!   !} ⟩
        {!   !}
    ≡Eq⟨ {!   !} ⟩
        {!   !}
    ≡Eq⟨ {!   !} ⟩
        {!   !}
    ≡Eq⟨ {!   !} ⟩
        {!   !}
    ∎Eq
-}

data System : (base from range : ℕ) → Set where
    Sys : ∀ {b m n} → List (Digit (suc b) m n) → System (suc b) m n
{-
_S+_ : ∀ {b m n} → System b m n → System b m n → System b m n
Sys []       S+ Sys ys = Sys ys
Sys xs       S+ Sys [] = Sys xs
Sys (x ∷ xs) S+ Sys (y ∷ ys) = {! x  !}


S→N : ∀ {b m n} → System b m n → ℕ
S→N {zero} ()
S→N {suc b} (Sys list) = foldr (shift-then-add (suc b)) 0 list
    where   shift-then-add : ∀ {m n} → (b : ℕ) → Digit b m n → ℕ → ℕ
            shift-then-add b x acc = (D→N x) + (acc * b)
-}
--
--  Example
--

private
    one : Digit 2 1 2
    one = D Fz

    two : Digit 2 1 2
    two = D (Fs Fz)

    u0 : Digit 1 0 2
    u0 = U0 Fz

    u1 : Digit 1 1 1
    u1 = U1 Fz

    a0 : Digit 3 0 4
    a0 = D Fz

    a1 : Digit 3 0 4
    a1 = D (Fs Fz)

    a2 : Digit 3 0 4
    a2 = D (Fs (Fs Fz))

    a3 : Digit 3 0 4
    a3 = D (Fs (Fs (Fs Fz)))


    a : System 2 1 2
    a = Sys (one ∷ two ∷ two ∷ [])
