module Data.Num where

open import Data.Nat
open import Data.Fin as Fin
    using (Fin; #_; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

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


toℕ : ∀ {b d o} → Num b d o → ℕ
toℕ             ∙        = 0
toℕ {b} {_} {o} (x ∷ xs) = Digit-toℕ x o + b * toℕ xs


------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

_≲_ : ∀ {b d o} → Num b d o → Num b d o → Set
xs ≲ ys = toℕ xs ≤ toℕ ys

_≋_ : ∀ {b d o} → Num b d o → Num b d o → Set
xs ≋ ys = toℕ xs ≡ toℕ ys

≋-isEquivalence : ∀ {b d o} → IsEquivalence {A = Num b d o} _≋_
≋-isEquivalence = record
    { refl = λ {x} → refl
    ; sym = sym
    ; trans = trans
    }

Num-Setoid : ∀ b d o → Setoid _ _
Num-Setoid b d o = record
    { Carrier = Num b d o
    ; _≈_ = _≋_
    ; isEquivalence = ≋-isEquivalence
    }

data WhySpurious : ℕ → ℕ → ℕ → Set where
    Base≡0          : ∀ {  d o}          → WhySpurious 0 d o
    NoDigits        : ∀ {b   o}          → WhySpurious b 0 o
    Offset≥2        : ∀ {b d o} → o ≥ 2 → WhySpurious b d o
    UnaryWithOnly0s :                      WhySpurious 1 1 0
    NotEnoughDigits : ∀ {b d o} → b ≥ 1 → d ≥ 1 → o < 2 → b ≰ d → WhySpurious b d o

data SurjectionView : ℕ → ℕ → ℕ → Set where
    WithZero : ∀ {b d} → (b≥1 : b ≥ 1) → (d≥2 : d ≥ 2) → (b≤d : b ≤ d) → SurjectionView b d 0
    Zeroless : ∀ {b d} → (b≥1 : b ≥ 1) → (d≥1 : d ≥ 1) → (b≤d : b ≤ d) → SurjectionView b d 1
    Spurious : ∀ {b d o} → WhySpurious b d o → SurjectionView b d o

surjectionView : (b d o : ℕ) → SurjectionView b d o
-- # base = 0
surjectionView 0             d             o = Spurious Base≡0
-- # base ≥ 1
surjectionView (suc b)       0             o = Spurious NoDigits
--      # starts from 0 (offset = 0)
surjectionView (suc b)       (suc d)       0 with suc b ≤? suc d
surjectionView 1             1             0 | yes p = Spurious UnaryWithOnly0s
surjectionView (suc (suc b)) 1             0 | yes (s≤s ())
surjectionView 1             (suc (suc d)) 0 | yes p = WithZero (s≤s z≤n) (s≤s (s≤s z≤n)) p
surjectionView (suc (suc b)) (suc (suc d)) 0 | yes p = WithZero (s≤s z≤n) (≤-trans (s≤s (s≤s z≤n)) p) p
    where   open import Data.Nat.Properties.Extra using (≤-trans)
surjectionView (suc b)       (suc d)       0 | no ¬p = Spurious (NotEnoughDigits (s≤s z≤n) (s≤s z≤n) (s≤s z≤n) ¬p)        -- not enough digits
--      # starts from 1 (offset = 1)
surjectionView (suc b)       (suc d)       1 with suc b ≤? suc d
surjectionView (suc b)       (suc d)       1 | yes p = Zeroless (s≤s z≤n) (s≤s z≤n) p
surjectionView (suc b)       (suc d)       1 | no ¬p = Spurious (NotEnoughDigits (s≤s z≤n) (s≤s z≤n) (s≤s (s≤s z≤n)) ¬p)        -- not enough digits

surjectionView (suc b)       (suc d)       (suc (suc o)) = Spurious (Offset≥2 (s≤s (s≤s z≤n)))    -- offset ≥ 2

notSpurious : ℕ → ℕ → ℕ → Set
notSpurious b d o = ∀ reason → surjectionView b d o ≢ Spurious reason

------------------------------------------------------------------------
-- Operations on Num
------------------------------------------------------------------------

open import Data.Nat.Properties using (≤⇒pred≤)
open import Data.Nat.Properties.Extra using (≤∧≢⇒<)
open import Data.Fin.Properties using (bounded)


digit+1-b-lemma : ∀ {b d} → (x : Digit d)
    → b ≥ 1 → suc (Fin.toℕ x) ≡ d
    → suc (Fin.toℕ x) ∸ b < d
digit+1-b-lemma {b} {d} x b≥1 p =
    start
        suc (suc (Fin.toℕ x) ∸ b)
    ≤⟨ s≤s (∸-mono ≤-refl b≥1) ⟩
        suc (Fin.toℕ x)
    ≤⟨ reflexive p ⟩
        d
    □
    where   open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
            open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)
            open import Data.Nat.Properties using (∸-mono)

digit+1-b : ∀ {b d} → (x : Digit d) → b ≥ 1 → suc (Fin.toℕ x) ≡ d → Fin d
digit+1-b {b} {d} x b≥1 p = fromℕ≤ {suc (Fin.toℕ x) ∸ b} (digit+1-b-lemma x b≥1 p)

digit+1 : ∀ {d} → (x : Digit d) → (¬p : suc (Fin.toℕ x) ≢ d) → Fin d
digit+1 x ¬p = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p)

1+ : ∀ {b d o}
    → Num b d o
    → Num b d o
1+ {b} {d} {o} xs with surjectionView b d o
1+ ∙        | WithZero b≥1 d≥2 b≤d = fromℕ≤ {1} d≥2 ∷ ∙                -- e.g.   ⇒ 1
1+ (x ∷ xs) | WithZero b≥1 d≥2 b≤d with full x
1+ (x ∷ xs) | WithZero b≥1 d≥2 b≤d | yes p = digit+1-b x b≥1 p ∷ 1+ xs  --      n ⇒ n + 1 - base
1+ (x ∷ xs) | WithZero b≥1 d≥2 b≤d | no ¬p = digit+1   x    ¬p ∷ xs     --      n ⇒ n + 1
1+ ∙        | Zeroless b≥1 d≥1 b≤d = fromℕ≤ {0} d≥1 ∷ ∙                -- e.g. 9 ⇒ 10
1+ (x ∷ xs) | Zeroless b≥1 d≥1 b≤d with full x
1+ (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | yes p = digit+1-b x b≥1 p ∷ 1+ xs  --      n ⇒ n + 1 - base
1+ (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | no ¬p = digit+1   x    ¬p ∷ xs     --      n ⇒ n + 1
1+ xs       | Spurious _ = xs


fromℕ : ∀ {b d o} → ℕ → Num b d o
fromℕ {b} {d} {o} n with surjectionView b d o
fromℕ zero    | WithZero b≥1 d≥2 b≤d = ∙
fromℕ (suc n) | WithZero b≥1 d≥2 b≤d = 1+ (fromℕ n)
fromℕ zero    | Zeroless b≥1 d≥1 b≤d = ∙
fromℕ (suc n) | Zeroless b≥1 d≥1 b≤d = 1+ (fromℕ n)
fromℕ n       | Spurious _ = ∙
