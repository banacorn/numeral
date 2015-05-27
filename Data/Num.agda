module Data.Num where

open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat as Nat using (ℕ; zero; suc; pred; s≤s; z≤n; ≤-pred; decTotalOrder)
    renaming (_+_ to _N+_; _∸_ to _N-_;
              _*_ to _N*_;
              _<_ to _N<_; _≤_ to _N≤_; _≤?_ to _N≤?_; _>_ to _N>_)
open Nat.≤-Reasoning

open import Data.Nat.DivMod
open import Data.Nat.Properties.Simple using (+-right-identity)
open import Data.Fin.Properties using (bounded)
open import Data.Fin using (Fin; inject₁; fromℕ≤)
    renaming (toℕ to Fin⇒ℕ; fromℕ to ℕ⇒Fin; zero to Fz; suc to Fs)
open import Data.Product
open import Data.Unit using (tt)
open import Relation.Nullary

open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary

open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; sym; trans)



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
    D1 : ∀ {  m n}
         → Fin n
         → {m≤n : m N≤ n}
         → Digit 1 m n
    Dn : ∀ {b m n}
         → Fin n
         → let base = suc (suc b) in
           {b≤n : base N≤ n} → {bm≤n : (base N* m) N≤ n}
         → Digit base m n

Digit⇒ℕ : ∀ {b m n} → Digit b m n → ℕ
Digit⇒ℕ {m = m} (D1 x) = m N+ Fin⇒ℕ x
Digit⇒ℕ {m = m} (Dn x) = m N+ Fin⇒ℕ x

_F-_ : ∀ {b n} → Fin n → Fin b → Fin n
Fz   F- y    = Fz
Fs x F- Fz   = Fs x
Fs x F- Fs y = inject₁ (x F- y)

-- lem : ∀ b x → Fin⇒ℕ (x mod (suc b)) N< suc b
-- lem b x = {!   !}
lem : ∀ b x → Fin⇒ℕ (x mod (suc b)) N< (suc b)
lem b x = bounded (x mod suc b)

lem0 : ∀ x y → (suc x) N- (suc y) N< (suc x)
lem0 zero y = {!   !}
lem0 (suc x) y = {!   !}

lem1 : ∀ a b c → c N< (suc b) → a N+ c N- (suc b) N< a
lem1 a b zero (s≤s z≤n) = {!   !}
lem1 a b (suc c) (s≤s c<a) = {!   !}

--
-- let remainder = sum `mod` base
--     Q         = n `div` base
-- in
--    if sum ≥ n
--        then    base * pred Q + remainder
--        else    sum
ℕ-isDecTotalOrder = DecTotalOrder.isDecTotalOrder decTotalOrder
ℕ-isTotalOrder = IsDecTotalOrder.isTotalOrder ℕ-isDecTotalOrder
ℕ-isPartialOrder = IsTotalOrder.isPartialOrder ℕ-isTotalOrder
ℕ-isPreorder = IsPartialOrder.isPreorder ℕ-isPartialOrder
≤-refl = IsPreorder.reflexive ℕ-isPreorder

_D+_ : ∀ {b m n} → Digit b m n → Digit b m n → Digit b m n
_D+_ {zero}            () ()
_D+_ {suc zero}        x  y  = x
_D+_ {suc (suc b)} {m} {n} (Dn x) (Dn y) with suc (m N+ Fin⇒ℕ x N+ Fin⇒ℕ y) N≤? n
_D+_ {suc (suc b)} (Dn x) (Dn y {b≤n} {bm≤n}) | yes p = Dn (fromℕ≤ b≤n)
_D+_ {suc (suc b)} {m} (Dn x) (Dn y) | no ¬p with (m N+ Fin⇒ℕ x N+ Fin⇒ℕ y) divMod (suc (suc b))
_D+_ {suc (suc b)} {m} {n} (Dn x) (Dn y {b≤n}) | no ¬p | result _ remainder property =
    let sum = m N+ Fin⇒ℕ x N+ Fin⇒ℕ y
        base = suc (suc b)
        Q = sum mod base
        sum' = (Fin⇒ℕ remainder) N+ (Fin⇒ℕ Q) N* base
    in  Dn {!   !}

{-
_D+_ {suc (suc b)} {m} {n} (Dn x) (Dn y {b≤n}) | no ¬p | result zero remainder property = contradiction
    (begin
        suc (m N+ Fin⇒ℕ x N+ Fin⇒ℕ y)
    ≡⟨ cong suc property ⟩
        suc (Fin⇒ℕ remainder N+ 0)
    ≡⟨ cong suc (+-right-identity (Fin⇒ℕ remainder)) ⟩
        suc (Fin⇒ℕ remainder)
    ≤⟨ bounded remainder ⟩
        suc (suc b)
    ≤⟨ b≤n ⟩
        n
    ∎) ¬p
_D+_ {suc (suc b)} {m} {n} (Dn x) (Dn y {b≤n}) | no ¬p | result (suc quotient) remainder property =
    let base = suc (suc b)
        sum = Fin⇒ℕ remainder N+ quotient N* base
        -- ¬p : sum ≥ n
        -- property : sum = Fin⇒ℕ remainder N+ (suc quotient) N* base
    in  Dn (fromℕ≤ {sum} (
            begin
                suc (Fin⇒ℕ remainder N+ quotient N* suc (suc b))
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!    !} ⟩
                {!    !}
            ≤⟨ {!    !} ⟩
                n
            ∎))
-}
{-
    begin
        {!   !}
    <⟨ {!   !} ⟩
        {!   !}
    ∎

    where
            ℕ-isDecTotalOrder = DecTotalOrder.isDecTotalOrder decTotalOrder
            ℕ-isTotalOrder = IsDecTotalOrder.isTotalOrder ℕ-isDecTotalOrder
            ℕ-isPartialOrder = IsTotalOrder.isPartialOrder ℕ-isTotalOrder
            ℕ-isPreorder = IsPartialOrder.isPreorder ℕ-isPartialOrder

            ≤-trans : ∀ {a b c} → a N≤ b → b N≤ c → a N≤ c
            ≤-trans = IsPreorder.trans ℕ-isPreorder
-}

--
--  Numeral System:
--
{-}
data System : (basse from range : ℕ) → Set where
    Sys : ∀ {b m n} → List (Digit m n) → System b m n

toℕ : ∀ {b m n} → System b m n → ℕ
toℕ {b} (Sys list) = foldr (shift-then-add b) 0 list
    where   shift-then-add : ∀ {m n} → (base : ℕ) → Digit m n → ℕ → ℕ
            shift-then-add b x acc = (Digit⇒ℕ x) ℕ+ (acc ℕ* b)

_+_ : ∀ {b m n} → System b m n → System b m n → System b m n
Sys []       + Sys ys = Sys ys
Sys xs       + Sys [] = Sys xs
Sys (x ∷ xs) + Sys (y ∷ ys) = {! x  !}

-}
--
--  Example
--

private
    one : Digit 2 1 2
    one = Dn Fz {s≤s (s≤s z≤n)} {s≤s (s≤s z≤n)}

    two : Digit 2 1 2
    two = Dn (Fs Fz) {s≤s (s≤s z≤n)} {s≤s (s≤s z≤n)}

    -- a : System 1 1 2
    -- a = Sys (one ∷ two ∷ [])
