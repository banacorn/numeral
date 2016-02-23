module Data.Num.Bijective where

-- open import Data.Nat using (ℕ; suc; zero; _≤?_; s≤s)
open import Data.Nat
open import Data.Fin as Fin using (Fin; #_; fromℕ≤)
    renaming (toℕ to F→N)

open import Data.Product
open import Level using () renaming (suc to lsuc)
open import Function
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; sym; trans; inspect)

infixr 2 [_]_

-- For a system to be bijective wrt ℕ:
--  * base ≥ 1
--  * digits = {1 .. base}
data Num : ℕ → Set where
    -- from the terminal object, which represents 0
    ∙ : ∀ {b}           -- base
        → Num (suc b)   -- base ≥ 1

    -- successors
    [_]_ : ∀ {b}
        → Fin b         -- digit = {1 .. b}
        → Num b → Num b

infixr 9 _/_
-- syntax sugar for chaining digits with ℕ
_/_ : ∀ {b} → (n : ℕ)
    → {lower-bound : True (suc zero ≤? n)}      -- digit ≥ 1
    → {upper-bound : True (n        ≤? b)}      -- digit ≤ base
    → Num b → Num b
_/_ {b} zero    {()} {ub} ns
_/_ {b} (suc n) {lb} {ub} ns = [ (# n) {b} {ub} ] ns

module _/_-Examples where

    零 : Num 2
    零 = ∙

    一 : Num 2
    一 = 1 / ∙

    八 : Num 3
    八 = 2 / 2 / ∙




toℕ : ∀ {b} → Num b → ℕ
toℕ ∙ = zero
toℕ ([ x ] xs) = digit→ℕ x + toℕ xs
    where
            digit→ℕ : ∀ {b} → Fin b → ℕ
            digit→ℕ i = suc (F→N i)


open import Induction.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Relation.Binary
open DecTotalOrder decTotalOrder
open ≤-Reasoning
open PropEq.≡-Reasoning
    renaming (begin_ to beginEq_; _≡⟨_⟩_ to _≡Eq⟨_⟩_; _∎ to _∎Eq)

fromℕ : ∀ {b} → ℕ → Num (suc b)
fromℕ {b} = <-rec _ go
    where
            prf0 : ∀ n Q → suc n ≡ suc (b + Q * suc b) → suc Q ≤′ suc n
            prf0 n Q prop = ≤⇒≤′ $ begin
                    suc Q
                ≤⟨ m≤m+n (suc Q) (b + Q * b) ⟩
                    suc Q + suc Q * b
                ≤⟨ reflexive $ sym $
                    beginEq
                        suc n
                    ≡Eq⟨ prop ⟩
                        suc Q * suc b
                    ≡Eq⟨ (+-*-suc (suc Q) b) ⟩
                        suc Q + (suc Q * b)
                    ∎Eq  ⟩
                    suc n
                ∎
            prf1 : ∀ n R Q → suc n ≡ suc (F→N R + Q * suc b) → suc Q ≤′ suc n
            prf1 n R Q prop = ≤⇒≤′ $ begin
                    suc Q
                ≤⟨ s≤s (m≤m+n Q (Q * b)) ⟩
                    suc (Q + Q * b)
                ≤⟨ s≤s (reflexive (sym (+-*-suc Q b))) ⟩
                    suc (Q * suc b)
                ≤⟨ s≤s (n≤m+n (F→N R) (Q * suc b)) ⟩
                    suc (F→N R + Q * suc b)
                ≤⟨ reflexive $ sym $
                    beginEq
                        suc n
                    ≡Eq⟨ prop ⟩
                        suc (F→N R + Q * suc b)
                    ∎Eq  ⟩
                    suc n
                ∎

            go : (x : ℕ) → ((y : ℕ) → suc y ≤′ x → Num (suc b)) → Num (suc b)
            go zero    _ = ∙
            go (suc n) rec with (suc n) divMod (suc b)
            go (suc n) rec | result zero Fin.zero prop = ∙
            go (suc n) rec | result (suc Q) Fin.zero    prop = [ Fin.fromℕ b ] rec Q (prf0 n Q prop)
            go (suc n) rec | result Q       (Fin.suc R) prop = [ Fin.inject₁ R ] rec Q (prf1 n R Q prop)


carry : ∀ {b} → ℕ → Num b → Num b
carry {zero} n ([ () ] xs)
carry {suc b} n ∙ = fromℕ n
carry {suc b} n ([ x ] xs) with (n + F→N x) divMod (suc b)
carry {suc b} n ([ x ] xs) | result zero    R prop = [ R ] xs
carry {suc b} n ([ x ] xs) | result (suc Q) R prop = [ R ] carry (suc Q) xs

add : ∀ {b} → Num b → Num b → Num b
add ∙ ys = ys
add xs ∙ = xs
add {zero} ([ () ] xs) ([ y ] ys)
add {suc b} ([ x ] xs) ([ y ] ys) with (suc (F→N x + F→N y)) divMod (suc b)
add {suc b} ([ x ] xs) ([ y ] ys) | result zero R prop = [ R ] (add xs ys)
add {suc b} ([ x ] xs) ([ y ] ys) | result (suc Q) R prop = [ R ] carry (suc Q) (add xs ys)
