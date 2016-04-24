module Data.Num.Core where


open import Data.Nat
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary
open import Function.Equality using (_⟶_)


-- For a system to be surjective with respect to ℕ:
-- * has zero
--     * base = 1 : {0, 1 ...}
--     * base = 2 : {0, 1 ...}
--     * base = 3 : {0, 1, 2 ...}
-- * zeroless
--     * base = 1 : {   1 ...}
--     * base = 2 : {   1, 2...}
--     * base = 3 : {   1, 2, 3...}

Digit : ℕ → Set
Digit = Fin

infixr 5 _∷_

data Num : ℕ → ℕ → ℕ → Set where
    ∙   : ∀ {b d o} → Num b d o
    _∷_ : ∀ {b d o} → Digit d → Num b d o → Num b d o


------------------------------------------------------------------------
-- Digit
------------------------------------------------------------------------

Digit-toℕ : ∀ {d} → Digit d → ℕ → ℕ
Digit-toℕ d o = o + Fin.toℕ d

-- A digit at its greatest
full : ∀ {d} (x : Fin d) → Dec (suc (Fin.toℕ x) ≡ d)
full {d} x = suc (Fin.toℕ x) ≟ d

------------------------------------------------------------------------
-- Conversion to ℕ
------------------------------------------------------------------------



toℕ : ∀ {b d o} → Num b d o → ℕ
toℕ             ∙        = 0
toℕ {b} {_} {o} (x ∷ xs) = Digit-toℕ x o + toℕ xs * b


------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

_≲_ : ∀ {b d o} → Num b d o → Num b d o → Set
xs ≲ ys = toℕ xs ≤ toℕ ys

_≋_ : ∀ {b d o} → Num b d o → Num b d o → Set
xs ≋ ys = toℕ xs ≡ toℕ ys


Num-Setoid : ∀ b d o → Setoid _ _
Num-Setoid b d o = record
    { Carrier = Num b d o
    ; _≈_ = _≋_
    ; isEquivalence = record
        { refl = λ {x} → refl
        ; sym = sym
        ; trans = trans
        }
    }

-- toℕ that preserves equality
Num⟶ℕ : ∀ b d o → setoid (Num b d o) ⟶ setoid ℕ
Num⟶ℕ b d o = record { _⟨$⟩_ = toℕ ; cong = cong toℕ }
