module Data.Num.Bijective where

-- open import Data.Nat using (ℕ; suc; zero; _≤?_; s≤s)
open import Data.Nat
open import Data.Fin as Fin using (Fin; #_; fromℕ≤)
open import Data.Fin.Properties using (bounded)
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open ≤-Reasoning
open import Level using () renaming (suc to lsuc)
open import Function
open import Relation.Nullary.Negation
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

open import Data.Nat.DivMod
open import Data.Nat.Properties using (≰⇒>)
open import Relation.Binary
-- open DecTotalOrder decTotalOrder hiding (_≤?_; _≤_; _≟_; refl)

toℕ : ∀ {b} → Num b → ℕ
toℕ ∙         = zero
toℕ {b} ([ x ] xs) = suc (Fin.toℕ x) + (toℕ xs * b)

digit+1-lemma : ∀ a b → a < suc b → a ≢ b → a < b
digit+1-lemma zero    zero    a<1+b a≢b = contradiction refl a≢b
digit+1-lemma zero    (suc b) a<1+b a≢b = s≤s z≤n
digit+1-lemma (suc a) zero    (s≤s ()) a≢b
digit+1-lemma (suc a) (suc b) (s≤s a<1+b) a≢b = s≤s (digit+1-lemma a b a<1+b (λ z → a≢b (cong suc z)))

digit+1 : ∀ {b} → (x : Fin (suc b)) → Fin.toℕ x ≢ b → Fin (suc b)
digit+1 {b} x ¬p = fromℕ≤ {suc (Fin.toℕ x)} (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p))

+1 : ∀ {b} → Num (suc b) → Num (suc b)
+1 ∙ = [ Fin.zero ] ∙
+1 {b} ([ x ] xs) with Fin.toℕ x ≟ b
+1 {b} ([ x ] xs) | yes p = [ Fin.zero ] +1 xs
+1 {b} ([ x ] xs) | no ¬p = [ digit+1 x ¬p ] xs

fromℕ : ∀ {b} → ℕ → Num (suc b)
fromℕ zero = ∙
fromℕ (suc n) = +1 (fromℕ n)

add : ∀ {b} → Num b → Num b → Num b
add ∙ ys = ys
add xs ∙ = xs
add {zero} ([ () ] xs) ([ y ] ys)
add {suc b} ([ x ] xs) ([ y ] ys) with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b)
add {suc b} ([ x ] xs) ([ y ] ys) | result zero R prop = [ R ] (add xs ys)
add {suc b} ([ x ] xs) ([ y ] ys) | result (suc Q) R prop = [ R ] +1 (add xs ys)

_≈_ : ∀ {b} → Num b → Num b → Set
∙          ≈ ∙          = ⊤
∙          ≈ ([ y ] ys) = ⊥
([ x ] xs) ≈ ∙          = ⊥
([ x ] xs) ≈ ([ y ] ys) with Fin.toℕ x ≟ Fin.toℕ y
([ x ] xs) ≈ ([ y ] ys) | yes p = xs ≈ ys
([ x ] xs) ≈ ([ y ] ys) | no ¬p = ⊥
