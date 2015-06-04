module Data.Num where

open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat
open ≤-Reasoning

open import Data.Nat.DivMod
open import Data.Nat.Properties using (m≤m+n; n≤m+n;_+-mono_)
open import Data.Nat.Properties.Simple using (+-right-identity; +-suc; +-assoc)
open import Data.Fin.Properties using (bounded)
open import Data.Fin using (Fin; fromℕ≤; inject≤)
    renaming (toℕ to Fin⇒ℕ; fromℕ to ℕ⇒Fin; zero to Fz; suc to Fs)
open import Data.Product
open import Data.Maybe

open import Function
open import Data.Unit using (tt)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (True; False; toWitness)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary

open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; sym; trans; inspect)

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
D→N {m = m} d = m + Fin⇒ℕ (D→F d)

private

    -- alias
    ℕ-isDecTotalOrder   = DecTotalOrder.isDecTotalOrder decTotalOrder
    ℕ-isTotalOrder      = IsDecTotalOrder.isTotalOrder ℕ-isDecTotalOrder
    ℕ-isPartialOrder    = IsTotalOrder.isPartialOrder ℕ-isTotalOrder
    ℕ-isPreorder        = IsPartialOrder.isPreorder ℕ-isPartialOrder
    ≤-refl      = IsPreorder.reflexive ℕ-isPreorder
    ≤-antisym   = IsPartialOrder.antisym ℕ-isPartialOrder
    ≤-total     = IsTotalOrder.total ℕ-isTotalOrder


    -- some boring lemmas

    >-complement : ∀ {a b} → a > b → ¬ (a ≤ b)
    >-complement {zero}  ()
    >-complement {suc a} {zero} a>b ()
    >-complement {suc a} {suc b} (s≤s a>b) = contraposition >-complement (λ z → z a>b)

    lem₁ : ∀ m k → suc (m + k) > m
    lem₁ zero k = s≤s z≤n
    lem₁ (suc m) k = s≤s (lem₁ m k)

    lem₂ : ∀ m n → n ≤ m → {≢0 : False (n ≟ 0)} → 0 < (_div_ m n {≢0})
    lem₂ m       zero    n≤m {()}
    lem₂ zero    (suc n) ()
    lem₂ (suc m) (suc n) n≤m {≢0} with compare m n
    lem₂ (suc m) (suc .(suc (m + k))) (s≤s n≤m) {tt} | less .m k    = contradiction n≤m (>-complement (lem₁ m k))
    lem₂ (suc m) (suc .m)              n≤m           | equal .m     = s≤s z≤n
    lem₂ (suc .(suc (n + k))) (suc n) n≤m            | greater .n k = s≤s z≤n


    lem₃ : ∀ m n → n ≤ m → {≢0 : False (n ≟ 0)} → m > Fin⇒ℕ (_mod_ m n {≢0})
    lem₃ m       zero    n≤m {()}
    lem₃ zero    (suc n) ()
    lem₃ (suc m) (suc n) n≤m {≢0} with _divMod_ (suc m) (suc n) {≢0} | inspect (λ x → _divMod_ (suc m) (suc n) {≢0 = x}) ≢0
    lem₃ (suc m) (suc n) n≤m {tt} | result zero remainder property | PropEq.[ eq ] =
        contradiction (≤-refl (cong DivMod.quotient eq)) (>-complement (lem₂ (suc m) (suc n) n≤m))
    lem₃ (suc m) (suc n) n≤m {tt} | result (suc quotient) remainder property | w =
        begin
            suc (Fin⇒ℕ remainder)
        ≤⟨ s≤s (m≤m+n (Fin⇒ℕ remainder) (n + quotient * suc n)) ⟩
            suc (Fin⇒ℕ remainder + (n + quotient * suc n))
        ≡⟨ sym (+-suc (Fin⇒ℕ remainder) (n + quotient * suc n)) ⟩
            Fin⇒ℕ remainder + suc (n + quotient * suc n)
        ≡⟨ sym property ⟩
            suc m
        ∎
    -- helper function for adding two 'Fin n' with offset 'm'
    -- (m + x) + (m + y) - m = m + x + y
    D+sum : ∀ {n} (m : ℕ) → (x y : Fin n) → ℕ
    D+sum m x y = m + (Fin⇒ℕ x) + (Fin⇒ℕ y)


--  if x D+ y overflown
--  let x D+ y be the largest digit that is congruent modulo b
--  for example, redundant binary number (b = 2, m = 0, n = 3)
--      1 + 2 ≡ 1 mod b
--      2 + 2 ≡ 2 mod b
--
--  Algorithm:
--  let sum      = x + y
--      sum%base = sum `mod` base
--      n%base   = n `mod` base
--      suc Q    = n `div` base
--  in
--      | sum < n = sum
--      | sum ≥ n, sum%base ≡ 0, n%base ≢ 0 = suc Q * base
--      | sum ≥ n = Q * base + sum%base

_D+_ : ∀ {b m n} → Digit b m n → Digit b m n →  Digit b m n
_D+_ {zero}                ()     ()
_D+_ {suc zero}            x      _      = x
_D+_ {suc (suc b)} {m} {n} (D x) (D y) with suc (D+sum m x y) ≤? n
_D+_ {suc (suc b)} {m} {n} (D x) (D y {b≤n} {bm≤n}) | yes p =
    D (fromℕ≤ {D+sum m x y} p) {b≤n} {bm≤n} -- just return the sum
_D+_ {suc (suc b)} {m} {n} (D x) (D y) | no ¬p with n divMod (suc (suc b)) | inspect (λ w → _divMod_ n (suc (suc b)) {≢0 = w}) tt
_D+_ {suc (suc b)} {m} {n} (D x) (D y {b≤n} {bm≤n}) | no ¬p | result zero n%base prop | PropEq.[ eq ] =
    -- prop   : n ≡ n%base + 0
    -- prop'  : n ≤ n%base
    -- lem₃   : n > n%base
    let base = suc (suc b)
        prop' =
            begin
                n
            ≡⟨ prop ⟩
                Fin⇒ℕ n%base + 0
            ≡⟨ +-right-identity (Fin⇒ℕ n%base) ⟩
                Fin⇒ℕ n%base
            ≡⟨ cong (λ w → Fin⇒ℕ (DivMod.remainder w)) (sym eq) ⟩
                Fin⇒ℕ (DivMod.remainder (n divMod suc (suc b)))
            ∎
        ¬lem₃ = >-complement (lem₃ n base (toWitness b≤n))
    in  contradiction prop' ¬lem₃
_D+_ {suc (suc b)} {m} {n} (D x) (D y {b≤n} {bm≤n}) | no ¬p | result (suc Q) n%base prop | PropEq.[ eq ] with D+sum m x y divMod (suc (suc b)) | inspect (λ w → _divMod_ (D+sum m x y) (suc (suc b)) {≢0 = w}) tt
_D+_ {suc (suc b)} {m} {n} (D x) (D y {b≤n} {bm≤n}) | no ¬p | result (suc Q) (Fs n%base) prop | PropEq.[ eq ] | result _ Fz _ | PropEq.[ eq₁ ] =
    -- the case when n%base ≢ 0 and sum%base ≡ 0
    let base = suc (suc b)
        sum = suc Q * base
        sum<n = begin
                suc sum
            ≤⟨ s≤s (n≤m+n (Fin⇒ℕ n%base) sum) ⟩
                suc (Fin⇒ℕ n%base + sum)
            ≡⟨ sym prop ⟩
                n
            ∎
    in  D (fromℕ≤ {sum} sum<n) {b≤n} {bm≤n}
_D+_ {suc (suc b)} {m} {n} (D x) (D y {b≤n} {bm≤n}) | no ¬p | result (suc Q) n%base prop | PropEq.[ eq ] | result _ sum%base property | PropEq.[ eq₁ ] =
    let base = suc (suc b)
        sum = Fin⇒ℕ sum%base + Q * base
        sum<n = begin
                suc (Fin⇒ℕ sum%base + Q * base)
            ≡⟨ sym (+-assoc 1 (Fin⇒ℕ sum%base) (Q * base)) ⟩
                suc (Fin⇒ℕ sum%base) + Q * base
            ≤⟨ bounded sum%base +-mono ≤-refl refl ⟩
                base + Q * base
            ≤⟨ n≤m+n (Fin⇒ℕ n%base) (base + Q * base) ⟩
                Fin⇒ℕ n%base + (base + Q * base)
            ≡⟨ sym prop ⟩
                n
            ∎
    in  D (fromℕ≤ {sum} sum<n) {b≤n} {bm≤n}


{-

_D⊕_ : ∀ {b m n} → Digit b m n → Digit b m n → Maybe (Digit b m n)
_D⊕_                       (D1 x) y = just y
_D⊕_ {suc (suc b)} {m} {n} (Dn x) (Dn y) with suc (D+sum m x y) ≤? n
_D⊕_ {suc (suc b)} {m} {n} (Dn x) (Dn y) | yes p = nothing
_D⊕_ {suc (suc b)} {m} {n} (Dn x) (Dn y {b≤n} {bm≤n}) | no ¬p =
    let base = suc (suc b)
        sum = D+sum m x y
        result quotient remainder property = _divMod_ sum base {tt}
    in  just {!   !}

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
-}

data System : (base from range : ℕ) → Set where
    Sys : ∀ {b m n} → List (Digit (suc b) m n) → System (suc b) m n

_S+_ : ∀ {b m n} → System b m n → System b m n → System b m n
Sys []       S+ Sys ys = Sys ys
Sys xs       S+ Sys [] = Sys xs
Sys (x ∷ xs) S+ Sys (y ∷ ys) = {! x  !}


S→N : ∀ {b m n} → System b m n → ℕ
S→N {zero} ()
S→N {suc b} (Sys list) = foldr (shift-then-add (suc b)) 0 list
    where   shift-then-add : ∀ {m n} → (b : ℕ) → Digit b m n → ℕ → ℕ
            shift-then-add b x acc = (D→N x) + (acc * b)

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
