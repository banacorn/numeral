module Data.Num.Bijective where

open import Data.Nat
open import Data.Fin as Fin using (Fin; #_; fromℕ≤)
open import Data.Fin.Extra
open import Data.Fin.Properties using (bounded)
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open import Level using () renaming (suc to lsuc)
open import Function
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq

infixr 5 _∷_

-- For a system to be bijective wrt ℕ:
--  * base ≥ 1
--  * digits = {1 .. base}
data Bij : ℕ → Set where
    -- from the terminal object, which represents 0
    ∙ : ∀ {b}           -- base
        → Bij (suc b)   -- base ≥ 1

    -- successors
    _∷_ : ∀ {b}
        → Fin b         -- digit = {1 .. b}
        → Bij b → Bij b

infixr 9 _/_
-- syntax sugar for chaining digits with ℕ
_/_ : ∀ {b} → (n : ℕ)
    → {lower-bound : True (suc zero ≤? n)}      -- digit ≥ 1
    → {upper-bound : True (n        ≤? b)}      -- digit ≤ base
    → Bij b → Bij b
_/_ {b} zero    {()} {ub} ns
_/_ {b} (suc n) {lb} {ub} ns = (# n) {b} {ub} ∷ ns

module _/_-Examples where

    零 : Bij 2
    零 = ∙

    一 : Bij 2
    一 = 1 / ∙

    八 : Bij 3
    八 = 2 / 2 / ∙

八 : Bij 3
八 = 2 / 2 / ∙

open import Data.Nat.DM
open import Data.Nat.Properties using (≰⇒>)
open import Relation.Binary

-- a digit at its largest
full : ∀ {b} (x : Fin (suc b)) → Dec (Fin.toℕ {suc b} x ≡ b)
full {b} x = Fin.toℕ x ≟ b

-- a digit at its largest (for ℕ)
full-ℕ : ∀ b n → Dec (n ≡ b)
full-ℕ b n = n ≟ b

------------------------------------------------------------------------
-- Digit
------------------------------------------------------------------------

digit-toℕ : ∀ {b} → Fin b → ℕ
digit-toℕ x = suc (Fin.toℕ x)

digit+1-lemma : ∀ a b → a < suc b → a ≢ b → a < b
digit+1-lemma zero    zero    a<1+b a≢b = contradiction refl a≢b
digit+1-lemma zero    (suc b) a<1+b a≢b = s≤s z≤n
digit+1-lemma (suc a) zero    (s≤s ()) a≢b
digit+1-lemma (suc a) (suc b) (s≤s a<1+b) a≢b = s≤s (digit+1-lemma a b a<1+b (λ z → a≢b (cong suc z)))

digit+1 : ∀ {b} → (x : Fin (suc b)) → Fin.toℕ x ≢ b → Fin (suc b)
digit+1 {b} x ¬p = fromℕ≤ {digit-toℕ x} (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p))

------------------------------------------------------------------------
-- Bij
------------------------------------------------------------------------

1+ : ∀ {b} → Bij (suc b) → Bij (suc b)
1+     ∙        = Fin.zero ∷ ∙
1+ {b} (x ∷ xs) with full x
1+ {b} (x ∷ xs) | yes p = Fin.zero ∷ 1+ xs
1+ {b} (x ∷ xs) | no ¬p = digit+1 x ¬p ∷ xs

n+ : ∀ {b} → ℕ → Bij (suc b) → Bij (suc b)
n+ zero    xs = xs
n+ (suc n) xs = 1+ (n+ n xs)

------------------------------------------------------------------------
-- From and to ℕ
------------------------------------------------------------------------

toℕ : ∀ {b} → Bij b → ℕ
toℕ ∙              = zero
toℕ {b} (x ∷ xs) = digit-toℕ x + (toℕ xs * b)

fromℕ : ∀ {b} → ℕ → Bij (suc b)
fromℕ zero    = ∙
fromℕ (suc n) = 1+ (fromℕ n)

------------------------------------------------------------------------
-- Functions on Bij
------------------------------------------------------------------------

-- infixl 6 _⊹_
--
-- _⊹_ : ∀ {b} → Bij b → Bij b → Bij b
-- _⊹_         ∙       ys        = ys
-- _⊹_         xs       ∙        = xs
-- _⊹_ {zero} (() ∷ xs) (y ∷ ys)
-- _⊹_ {suc b} (x ∷ xs) (y ∷ ys) with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b)
-- _⊹_ {suc b} (x ∷ xs) (y ∷ ys) | result quotient remainder property div-eq mod-eq =
--     remainder ∷ n+ quotient (xs ⊹ ys)


-- old base = suc b
-- new base = suc (suc b)
increase-base : ∀ {b} → Bij (suc b) → Bij (suc (suc b))
increase-base {b} ∙        = ∙
increase-base {b} (x ∷ xs) with fromℕ {suc b} (toℕ (increase-base xs) * suc b)
    | inspect (λ ws → fromℕ {suc b} (toℕ ws * suc b)) (increase-base xs)
increase-base {b} (x ∷ xs) | ∙      | [ eq ] = Fin.inject₁ x ∷ ∙
increase-base {b} (x ∷ xs) | y ∷ ys | [ eq ]
    with suc (Fin.toℕ x + Fin.toℕ y) divMod (suc (suc b))
increase-base {b} (x ∷ xs) | y ∷ ys | [ eq ]
    | result quotient remainder property div-eq mod-eq =
    remainder ∷ n+ quotient ys


-- old base = suc (suc b)
-- new base = suc b
decrease-base : ∀ {b} → Bij (suc (suc b)) → Bij (suc b)
decrease-base {b} ∙ = ∙
decrease-base {b} (x ∷ xs) with fromℕ {b} (toℕ (decrease-base xs) * suc (suc b))
              | inspect (λ ws → fromℕ {b} (toℕ ws * suc (suc b))) (decrease-base xs)
decrease-base {b} (x ∷ xs) | ∙      | [ eq ] with full x
decrease-base {b} (x ∷ xs) | ∙      | [ eq ] | yes p = Fin.zero ∷ Fin.zero ∷ ∙
decrease-base {b} (x ∷ xs) | ∙      | [ eq ] | no ¬p = inject-1 x ¬p ∷ ∙
decrease-base {b} (x ∷ xs) | y ∷ ys | [ eq ] with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b)
decrease-base (x ∷ xs) | y ∷ ys | [ eq ] | result quotient remainder property div-eq mod-eq
    = remainder ∷ n+ quotient ys
