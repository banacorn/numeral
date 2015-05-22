module Data.Num where

open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
    renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _<_ to _ℕ<_)
open import Data.Fin using (Fin; fromℕ≤)
    renaming (toℕ to Fin⇒ℕ; zero to Fz; suc to Fs)
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; sym; trans)


-- Surjective (ℕm):
--  base = 1, digits = {m ... n}, m ≥ 1, n ≥ 2m - 1
--  base > 1, digits = {m ... n}, m ≥ 0, n ≥ min (m + base - 1) (base × m)
-- Bijective:
--  base ≥ 1, digits = {1 .. base}

--
--  Digits:
--    Digit m n represents a Digit ranging from m to (m + n - 1)
--    e.g. Digit 0 2 = {0, 1}         for ordinary binary number
--         Digit 1 2 = {1, 2}         for zeroless binary number
--         Digit 0 3 = {0, 1, 2}      for redundant binary number
--

data Digit : (from range : ℕ) → Set where
    Dig : ∀ {m n} → Fin n → Digit m n

Digit⇒ℕ : ∀ {m n} → Digit m n → ℕ
Digit⇒ℕ {m} (Dig x) = (Fin⇒ℕ x) ℕ+ m

--
--  Numeral System:
--

data System : (base from range : ℕ) → Set where
    Sys : ∀ {b m n} → List (Digit m n) → System b m n

toℕ : ∀ {b m n} → System b m n → ℕ
toℕ {b} (Sys list) = foldr (shift-then-add b) 0 list
    where   shift-then-add : ∀ {m n} → (base : ℕ) → Digit m n → ℕ → ℕ
            shift-then-add b x acc = (Digit⇒ℕ x) ℕ+ (acc ℕ* b)

--
--  Example
--

private
    one : Digit 1 2
    one = Dig Fz

    two : Digit 1 2
    two = Dig (Fs Fz)

    a : System 2 1 2
    a = Sys (one ∷ two ∷ [])
