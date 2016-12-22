module Data.Num.Core where

open import Data.Num.Digit public

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤; toℕ; zero; suc; #_)
open import Data.Fin.Properties as FinProps using (bounded; toℕ-fromℕ≤)

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Function.Equality using (_⟶_)

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)


------------------------------------------------------------------------
-- Numbers
------------------------------------------------------------------------

infixr 5 _∷_

data Numeral : ℕ → ℕ → ℕ → Set where
    _∙  : ∀ {b d o} → Digit d → Numeral b d o
    _∷_ : ∀ {b d o} → Digit d → Numeral b d o → Numeral b d o

MMXVI : Numeral 10 10 0
MMXVI = # 6 ∷ # 1 ∷ # 0 ∷ (# 2) ∙


------------------------------------------------------------------------
-- Converting from Numeral to ℕ
------------------------------------------------------------------------

⟦_⟧ : ∀ {b d o} → (xs : Numeral b d o) → ℕ
⟦_⟧ {_} {_} {o} (x ∙)    = Digit-toℕ x o
⟦_⟧ {b} {_} {o} (x ∷ xs) = Digit-toℕ x o + ⟦ xs ⟧ * b

Num-lower-bound : ∀ {b d o}
    → (xs : Numeral b (suc d) o)
    → ⟦ xs ⟧ ≥ o
Num-lower-bound {_} {_} {o} (x ∙) = Digit-lower-bound o x
Num-lower-bound {b} {d} {o} (x ∷ xs) =
    start
        o
    ≤⟨ m≤m+n o (⟦ xs ⟧ * b) ⟩
        o + ⟦ xs ⟧ * b
    ≤⟨ +n-mono (⟦ xs ⟧ * b) (Digit-lower-bound o x) ⟩
        Digit-toℕ x o + ⟦ xs ⟧ * b
    □

-- the least significant digit
lsd : ∀ {b d o} → (xs : Numeral b d o) → Digit d
lsd (x ∙   ) = x
lsd (x ∷ xs) = x

lsd-toℕ : ∀ {b d o} → (xs : Numeral b d o) → Digit-toℕ (lsd xs) o ≤ ⟦ xs ⟧
lsd-toℕ (x ∙) = ≤-refl
lsd-toℕ {b} {d} {o} (x ∷ xs) = m≤m+n (Digit-toℕ x o) (⟦ xs ⟧ * b)

------------------------------------------------------------------------
-- View of Num
------------------------------------------------------------------------

data NumView : ℕ → ℕ → ℕ → Set where
    NullBase    : ∀   d o                            → NumView 0       (suc d) o
    NoDigits    : ∀ b o                              → NumView b       0       o
    AllZeros    : ∀ b                                → NumView (suc b) 1       0
    Proper      : ∀ b d o → (proper : suc d + o ≥ 2) → NumView (suc b) (suc d) o

numView : ∀ b d o → NumView b d o
numView b       zero          o       = NoDigits b o
numView zero    (suc d)       o       = NullBase d o
numView (suc b) (suc zero)    zero    = AllZeros b
numView (suc b) (suc zero)    (suc o) = Proper b zero (suc o) (s≤s (s≤s z≤n))
numView (suc b) (suc (suc d)) o       = Proper b (suc d) o (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Properties of Num
------------------------------------------------------------------------

NoDigits-explode : ∀ {b o a} {Whatever : Set a}
    → (xs : Numeral b 0 o)
    → Whatever
NoDigits-explode (() ∙   )
NoDigits-explode (() ∷ xs)

toℕ-NullBase : ∀ {d o}
    → (x : Digit d)
    → (xs : Numeral 0 d o)
    → ⟦ x ∷ xs ⟧ ≡ Digit-toℕ x o
toℕ-NullBase {d} {o} x xs =
    begin
        Digit-toℕ x o + ⟦ xs ⟧ * 0
    ≡⟨ cong (λ w → Digit-toℕ x o + w) (*-right-zero ⟦ xs ⟧) ⟩
        Digit-toℕ x o + 0
    ≡⟨ +-right-identity (Digit-toℕ x o) ⟩
        Digit-toℕ x o
    ∎

toℕ-AllZeros : ∀ {b} → (xs : Numeral b 1 0) → ⟦ xs ⟧ ≡ 0
toℕ-AllZeros     (z    ∙   ) = refl
toℕ-AllZeros     (s () ∙   )
toℕ-AllZeros {b} (z    ∷ xs) = cong (λ w → w * b) (toℕ-AllZeros xs)
toℕ-AllZeros     (s () ∷ xs)

n∷-mono-strict : ∀ {b d o}
    → (x : Fin d) (xs : Numeral (suc b) d o)
    → (y : Fin d) (ys : Numeral (suc b) d o)
    → Digit-toℕ x o ≡ Digit-toℕ y o
    → ⟦ xs ⟧ < ⟦ ys ⟧
    → ⟦ x ∷ xs ⟧ < ⟦ y ∷ ys ⟧
n∷-mono-strict {b} {d} {o} x xs y ys ⟦x⟧≡⟦y⟧ ⟦xs⟧<⟦ys⟧ =
    start
        suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
    ≈⟨ sym (+-suc (Digit-toℕ x o) (⟦ xs ⟧ * suc b)) ⟩
        Digit-toℕ x o + suc (⟦ xs ⟧ * suc b)
    ≤⟨ n+-mono (Digit-toℕ x o) (s≤s (n≤m+n b (⟦ xs ⟧ * suc b))) ⟩
        Digit-toℕ x o + (suc ⟦ xs ⟧) * suc b
    ≤⟨ (reflexive ⟦x⟧≡⟦y⟧) +-mono (*n-mono (suc b) ⟦xs⟧<⟦ys⟧) ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □


∷ns-mono-strict : ∀ {b d o}
    → (x : Fin d) (xs : Numeral b d o)
    → (y : Fin d) (ys : Numeral b d o)
    → ⟦ xs ⟧ ≡ ⟦ ys ⟧
    → Digit-toℕ x o < Digit-toℕ y o
    → ⟦ x ∷ xs ⟧ < ⟦ y ∷ ys ⟧
∷ns-mono-strict {b} {d} {o} x xs y ys ⟦xs⟧≡⟦ys⟧ ⟦x⟧<⟦y⟧ =
    start
        suc ⟦ x ∷ xs ⟧
    ≤⟨ ⟦x⟧<⟦y⟧ +-mono *n-mono b (reflexive ⟦xs⟧≡⟦ys⟧) ⟩
        ⟦ y ∷ ys ⟧
    □

tail-mono-strict : ∀ {b d o}
    → (x : Fin d) (xs : Numeral b d o)
    → (y : Fin d) (ys : Numeral b d o)
    → Greatest x
    → ⟦ x ∷ xs ⟧ < ⟦ y ∷ ys ⟧
    → ⟦ xs ⟧ < ⟦ ys ⟧
tail-mono-strict {b} {_} {o} x xs y ys greatest p
    = *n-mono-strict-inverse b ⟦∷xs⟧<⟦∷ys⟧
    where
        ⟦x⟧≥⟦y⟧ : Digit-toℕ x o ≥ Digit-toℕ y o
        ⟦x⟧≥⟦y⟧ = greatest-of-all o x y greatest
        ⟦∷xs⟧<⟦∷ys⟧ : ⟦ xs ⟧ * b < ⟦ ys ⟧ * b
        ⟦∷xs⟧<⟦∷ys⟧ = +-mono-contra ⟦x⟧≥⟦y⟧ p

tail-mono-strict-Null : ∀ {b d o}
    → (x : Fin d)
    → (y : Fin d) (ys : Numeral b d o)
    → Greatest x
    → ⟦ _∙ {b} {d} {o} x ⟧ < ⟦ y ∷ ys ⟧
    → 0 < ⟦ ys ⟧
tail-mono-strict-Null {b} {_} {o} x y ys greatest p
    = *n-mono-strict-inverse b ⟦∷∙⟧<⟦∷ys⟧
    where
        ⟦x⟧≥⟦y⟧ : Digit-toℕ x o ≥ Digit-toℕ y o
        ⟦x⟧≥⟦y⟧ = greatest-of-all o x y greatest
        ⟦∷∙⟧<⟦∷ys⟧ : 0 < ⟦ ys ⟧ * b
        ⟦∷∙⟧<⟦∷ys⟧ = +-mono-contra ⟦x⟧≥⟦y⟧ $
            start
                suc (Digit-toℕ x o) + 0
            ≈⟨ +-right-identity (suc (Digit-toℕ x o)) ⟩
                suc (Digit-toℕ x o)
            ≤⟨ p ⟩
                ⟦ y ∷ ys ⟧
            □
