module Data.Num where

open import Data.Nat
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open import Data.Fin as Fin
    using (Fin; #_; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Relation.Nullary
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
-- open ≡-Reasoning

-- open import Data.Fin.Properties using (bounded; toℕ-fromℕ≤)
-- open import Data.Nat.Properties
-- open import Data.Nat.Properties.Extra
-- open import Data.Nat.Properties.Simple

-- open import Data.Fin.Properties renaming (_≟_ to _F≟_)

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

data SurjectionView : ℕ → ℕ → ℕ → Set where
    WithZero : ∀ {b d} → (d≥2 : d ≥ 2) → SurjectionView b d 0
    Zeroless : ∀ {b d} → (d≥1 : d ≥ 1) → SurjectionView b d 1
    Spurious  : ∀ {b d o} → SurjectionView b d o

surjectionView : (b d o : ℕ) → SurjectionView b d o
-- # base = 0
surjectionView 0             d             o = Spurious
-- # base ≥ 1
surjectionView (suc b)       0             o = Spurious
--      # starts from 0 (offset = 0)
surjectionView (suc b)       (suc d)       0 with suc b ≤? suc d
surjectionView (suc b)       1             0 | yes p = Spurious     -- Unary number that possesses only 1 digit: { 0 }
surjectionView 1             (suc (suc d)) 0 | yes p = WithZero (s≤s (s≤s z≤n))
surjectionView (suc (suc b)) (suc (suc d)) 0 | yes p = WithZero (≤-trans (s≤s (s≤s z≤n)) p)
    where   open import Data.Nat.Properties.Extra using (≤-trans)
surjectionView (suc b)       (suc d)       0 | no ¬p = Spurious         -- not enough digits
--      # starts from 1 (offset = 1)
surjectionView (suc b)       (suc d)       1 with suc b ≤? suc d
surjectionView (suc b)       (suc d)       1 | yes p = Zeroless (s≤s z≤n)
surjectionView (suc b)       (suc d)       1 | no ¬p = Spurious         -- not enough digits

surjectionView (suc b)       (suc d)       (suc (suc o)) = Spurious     -- offset ≥ 2

------------------------------------------------------------------------
-- Operations on Num
------------------------------------------------------------------------

open import Data.Nat.Properties using (≤⇒pred≤)
open import Data.Nat.Properties.Extra using (≤∧≢⇒<)
open import Data.Fin.Properties using (bounded)

1+ : ∀ {b d o} → (view : SurjectionView b d o) → Num b d o → Num b d o
1+ (WithZero d≥2) ∙        = fromℕ≤ {1} d≥2 ∷ ∙                                              -- 0 ⇒ 1
1+ (WithZero d≥2) (x ∷ xs) with full x
1+ (WithZero d≥2) (x ∷ xs) | yes p = fromℕ≤ {0} (≤⇒pred≤ 2 _ d≥2) ∷ 1+ (WithZero d≥2) xs    -- 9 ⇒ 10
1+ (WithZero d≥2) (x ∷ xs) | no ¬p = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p) ∷ xs   -- 8 ⇒ 9
1+ (Zeroless d≥1) ∙        = fromℕ≤ {0} d≥1 ∷ ∙ -- ∙ ⇒ 1
1+ (Zeroless d≥1) (x ∷ xs) with full x
1+ (Zeroless d≥1) (x ∷ xs) | yes p = fromℕ≤ {0} d≥1 ∷ 1+ (Zeroless d≥1) xs                    -- A ⇒ 11
1+ (Zeroless d≥1) (x ∷ xs) | no ¬p = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p) ∷ xs   -- 8 ⇒ 9
1+ Spurious       xs       = xs -- stays the same (this is completely arbitrary), since we have no idea if there exists a successor  




-- open import Relation.Binary.PropositionalEquality.Core as PropEqCore
-- open import Relation.Nullary.Negation
-- open import Relation.Nullary.Decidable
-- open import Relation.Binary
-- open import Function
-- open import Function.Equality as FunEq hiding (setoid; id; _∘_; cong)
-- open import Function.Surjection hiding (id; _∘_)
-- open import Data.Unit using (⊤; tt)
-- open import Data.Empty using (⊥)

-- ------------------------------------------------------------------------
-- -- Surjectivity
-- ------------------------------------------------------------------------
--
-- _≲_ : ∀ {b d o} → Num b d o → Num b d o → Set
-- xs ≲ ys = toℕ xs ≤ toℕ ys
--
--
--
--
-- _≋_ : ∀ {b d o} → Num b d o → Num b d o → Set
-- xs ≋ ys = toℕ xs ≡ toℕ ys
--
-- ≋-isEquivalence : ∀ {b d o} → IsEquivalence {A = Num b d o} _≋_
-- ≋-isEquivalence = record
--     { refl = λ {x} → refl
--     ; sym = sym
--     ; trans = trans
--     }
--
-- Num-Setoid : ∀ b d o → Setoid _ _
-- Num-Setoid b d o = record
--     { Carrier = Num b d o
--     ; _≈_ = _≋_
--     ; isEquivalence = ≋-isEquivalence
--     }
--
-- Num⟶ℕ : ∀ b d o → Num-Setoid b d o ⟶ setoid ℕ
-- Num⟶ℕ b d o = record
--     { _⟨$⟩_ = toℕ
--     ; cong = id }
--
--
--
--
-- data SurjectionView : ℕ → ℕ → ℕ → Set where
--     WithZero : ∀ {b d} → (#digit≥2 : d ≥ 2) → SurjectionView b d 0
--     Zeroless : ∀ {b d} → (#digit≥1 : d ≥ 1) → SurjectionView b d 1
--     Spurious  : ∀ {b d o} → SurjectionView b d o
--
-- surjectionView : (b d o : ℕ) → SurjectionView b d o
-- surjectionView 0             _             _ = Spurious
-- surjectionView (suc b)       0             _ = Spurious
-- -- starts from 0
-- surjectionView (suc b)       (suc d)       0 with b ≤? d
-- surjectionView 1 1 0 | yes p = Spurious
-- surjectionView (suc zero) (suc (suc d)) zero | yes p = WithZero (s≤s (s≤s z≤n))
-- surjectionView (suc (suc b)) (suc d) zero | yes p = WithZero (s≤s {!    !})
-- surjectionView (suc b)       (suc d)       0 | no ¬p = Spurious
-- -- surjectionView 1             1             0 = Spurious -- Unary number that possesses only a digit 0
-- -- surjectionView 1             (suc (suc d)) 0 = WithZero (s≤s (s≤s z≤n))
-- -- surjectionView (suc (suc b)) (suc d)       0 with suc b ≤? d
-- -- surjectionView (suc (suc b)) (suc d)       0 | yes p = WithZero $ start
-- --         2
-- --     ≤⟨ s≤s (s≤s z≤n) ⟩
-- --         2 + b
-- --     ≤⟨ s≤s p ⟩
-- --         1 + d
-- --     □
-- -- surjectionView (suc (suc b)) (suc d)       0 | no ¬p = Spurious
-- -- starts from 1
-- surjectionView (suc b)       (suc d)       1 with suc b ≤? suc d
-- surjectionView (suc b)       (suc d)       1 | yes p = Zeroless (s≤s z≤n)
-- surjectionView (suc b)       (suc d)       1 | no ¬p = Spurious
-- -- offset ≥ 2
-- surjectionView (suc b)       (suc d)  (suc (suc o)) = Spurious
--
--
-- 1+ : ∀ {b d o} → (view : SurjectionView b d o) → Num b d o → Num b d o
-- 1+ (WithZero #digit≥2) ∙        = fromℕ≤ {1} #digit≥2 ∷ ∙
-- 1+ (WithZero #digit≥2) (x ∷ xs) = {!   !}
-- -- 1+ (WithZero #digit≥2) (x ∷ xs) with full x
-- -- 1+ (WithZero #digit≥2) (x ∷ xs) | yes p = fromℕ≤ {0}                (≤⇒pred≤ 2 _ #digit≥2) ∷ 1+ (WithZero #digit≥2) xs
-- -- 1+ (WithZero #digit≥2) (x ∷ xs) | no ¬p = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p) ∷ xs
-- 1+ (Zeroless #digit≥1) ∙        = fromℕ≤ #digit≥1 ∷ ∙
-- 1+ (Zeroless #digit≥1) (x ∷ xs) with full x
-- 1+ (Zeroless #digit≥1) (x ∷ xs) | yes p = fromℕ≤ #digit≥1 ∷ 1+ (Zeroless #digit≥1) xs
-- 1+ (Zeroless #digit≥1) (x ∷ xs) | no ¬p = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p) ∷ xs
-- 1+ Spurious xs = xs
-- -- 1+ : ∀ {b d o} → Num b d o → Num b d o
-- -- 1+ {b} {d} {o} xs with surjectionView b d o
-- -- 1+ ∙        | WithZero  #digit≥1 = fromℕ≤ #digit≥1 ∷ ∙
-- -- 1+ (x ∷ xs) | WithZero  _        with full x
-- -- 1+ (x ∷ xs) | WithZero  #digit≥1 | yes p = fromℕ≤ #digit≥1 ∷ 1+ xs
-- -- 1+ (x ∷ xs) | WithZero  _        | no ¬p = (fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p)) ∷ xs
-- -- 1+ ∙        | Zeroless #digit≥1 = fromℕ≤ #digit≥1 ∷ ∙
-- -- 1+ (x ∷ xs) | Zeroless _        with full x
-- -- 1+ (x ∷ xs) | Zeroless #digit≥1 | yes p = fromℕ≤ #digit≥1 ∷ 1+ xs
-- -- 1+ (x ∷ xs) | Zeroless _        | no ¬p = (fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p)) ∷ xs
-- -- 1+ xs       | Spurious = xs
--
-- -- begin
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ∎
--
-- toℕ-1+ : ∀ {b d o} → (view : SurjectionView b d o) → (xs : Num b d o) → toℕ (1+ view xs) ≡ suc (toℕ xs)
-- toℕ-1+ {b} (WithZero #digit≥2) ∙ =
--     begin
--         Fin.toℕ (fromℕ≤ #digit≥2) + b * zero
--     ≡⟨ cong (λ x → Fin.toℕ (fromℕ≤ #digit≥2) + x) (*-right-zero b) ⟩
--         Fin.toℕ (fromℕ≤ #digit≥2) + zero
--     ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ #digit≥2)) ⟩
--         Fin.toℕ (fromℕ≤ #digit≥2)
--     ≡⟨ toℕ-fromℕ≤ #digit≥2 ⟩
--         suc zero
--     ∎
-- toℕ-1+ {zero} (WithZero #digit≥2) (x ∷ xs) = {!   !}
-- toℕ-1+ {suc b} (WithZero #digit≥2) (x ∷ xs) = {!   !}
-- -- toℕ-1+ {b} {d} (WithZero #digit≥2) (x ∷ xs) | yes p =
-- --     begin
-- --         Fin.toℕ (fromℕ≤ (≤⇒pred≤ 2 _ #digit≥2)) + b * toℕ (1+ (WithZero #digit≥2) xs)
-- --     ≡⟨ cong (λ w → w + b * toℕ (1+ (WithZero #digit≥2) xs)) (toℕ-fromℕ≤ (≤⇒pred≤ 2 _ #digit≥2)) ⟩
-- --         b * toℕ (1+ (WithZero #digit≥2) xs)
-- --     ≡⟨ cong (λ w → b * w) (toℕ-1+ (WithZero #digit≥2) xs) ⟩
-- --         b * suc (toℕ xs)
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         d + b * toℕ xs
-- --     ≡⟨ cong (λ w → w + b * toℕ xs) (sym p) ⟩
-- --         suc (Fin.toℕ x + b * toℕ xs)
-- --     ∎
--     -- begin
--     --     Fin.toℕ (fromℕ≤ #digit≥2) + b * toℕ (1+ (WithZero #digit≥2) xs)
--     -- ≡⟨ cong (λ w → w + b * toℕ (1+ (WithZero #digit≥2) xs)) (toℕ-fromℕ≤ #digit≥2) ⟩
--     --     suc (b * toℕ (1+ (WithZero #digit≥2) xs))
--     -- ≡⟨ cong (λ w → suc (b * w)) (toℕ-1+ (WithZero #digit≥2) xs) ⟩
--     --     suc (b * suc (toℕ xs)) -- suc (b + b * toℕ xs)
--     -- ≡⟨ {!   !} ⟩
--     --     {!   !}
--     -- ≡⟨ {!   !} ⟩
--     --     {!   !}
--     -- ≡⟨ {!   !} ⟩
--     --     d + b * toℕ xs
--     -- ≡⟨ cong (λ w → w + b * toℕ xs) (sym p) ⟩
--     --     suc (Fin.toℕ x + b * toℕ xs)
--     -- ∎
-- -- toℕ-1+ {b} (WithZero #digit≥2) (x ∷ xs) | no ¬p = {!   !}
-- toℕ-1+ (Zeroless #digit≥1) xs = {!   !}
-- toℕ-1+ Spurious xs = {!   !}
--
-- fromℕ : ∀ {b d o} → SurjectionView b d o → ℕ → Num b d o
-- fromℕ (WithZero _       ) zero = ∙
-- fromℕ (WithZero p) (suc n) = 1+ (WithZero p) (fromℕ (WithZero p) n)
-- fromℕ (Zeroless _       ) zero = ∙
-- fromℕ (Zeroless p) (suc n) = 1+ (Zeroless p) (fromℕ (Zeroless p) n)
-- fromℕ Spurious n = ∙
-- --
-- 1+-fromℕ : ∀ {b d o} → (view : SurjectionView b d o) → (n : ℕ) → 1+ view (fromℕ view n) ≡ fromℕ view (suc n)
-- 1+-fromℕ (WithZero _) n = refl
-- 1+-fromℕ (Zeroless _) n = refl
-- 1+-fromℕ Spurious n = refl
--
--
-- -- fromℕ b d  o n       with surjectionView b d o
-- -- fromℕ b d .0 zero    | WithZero #digit≥1 = ∙
-- -- fromℕ b d .0 (suc n) | WithZero #digit≥1 = 1+ (fromℕ b d 0 n)
-- -- fromℕ b d .1 zero    | Zeroless #digit≥1 = ∙
-- -- fromℕ b d .1 (suc n) | Zeroless #digit≥1 = 1+ (fromℕ b d 1 n)
-- -- fromℕ b d  o n       | Spurious = ∙
-- -- fromℕ : ∀ b d o → ℕ → Num b d o
-- -- fromℕ b d  o n       with surjectionView b d o
-- -- fromℕ b d .0 zero    | WithZero #digit≥1 = ∙
-- -- fromℕ b d .0 (suc n) | WithZero #digit≥1 = 1+ (fromℕ b d 0 n)
-- -- fromℕ b d .1 zero    | Zeroless #digit≥1 = ∙
-- -- fromℕ b d .1 (suc n) | Zeroless #digit≥1 = 1+ (fromℕ b d 1 n)
-- -- fromℕ b d  o n       | Spurious = ∙
-- --
--
--
--
-- -- fromℕ that preserve equality
-- ℕ⟶Num : ∀ {b d o} → SurjectionView b d o → setoid ℕ ⟶ Num-Setoid b d o
-- ℕ⟶Num view = record
--     { _⟨$⟩_ = fromℕ view
--     ; cong = cong (toℕ ∘ fromℕ view)
--     }
-- -- ℕ⟶Num (Zeroless {b} {d} #digit≥1) = record { _⟨$⟩_ = ? ; cong = cong (toℕ ∘ fromℕb d 1) }
-- -- ℕ⟶Num {b} {d} {o} Spurious = record { _⟨$⟩_ = f ; cong = cong (toℕ ∘ fromℕ b d o) }
-- -- ℕ⟶Num : ∀ b d o → setoid ℕ ⟶ Num-Setoid b d o
-- -- ℕ⟶Num b d o = record
-- --     { _⟨$⟩_ = fromℕ b d o
-- --     ; cong = cong (toℕ ∘ fromℕ b d o) }
--
-- Surjective? : (b d o : ℕ) → Dec (Surjective {From = Num-Setoid b d o} {To = setoid ℕ} (Num⟶ℕ b d o))
-- Surjective? b d o with surjectionView b d o
-- Surjective? b d .0 | WithZero p = yes (record
--     { from = ℕ⟶Num (WithZero p)
--     ; right-inverse-of = {!   !}
--     })
--     -- where   proof : ∀ n → toℕ (fromℕ (WithZero p) n) ≡ n
--     --         proof zero = refl
--     --         proof (suc n) =
--     --             begin
--     --                 toℕ (1+ (WithZero p) (fromℕ (WithZero p) n))
--     --             ≡⟨ cong toℕ (1+-fromℕ (WithZero p) n) ⟩
--     --                 toℕ (1+ (WithZero p) (fromℕ (WithZero p) n))
--     --             ≡⟨ {!   !} ⟩
--     --                 {!   !}
--     --             ≡⟨ {!   !} ⟩
--     --                 {!   !}
--     --             ≡⟨ {!   !} ⟩
--     --                 {!   !}
--     --             ∎
--
--
--
-- Surjective? b d .1 | Zeroless #digit≥1 = yes {!   !}
-- Surjective? b d o  | Spurious = no {!   !}
--
-- --
-- -- mutual
-- --     Surjective? : (b d o : ℕ) → Dec (Surjective {From = Num-Setoid b d o} {To = setoid ℕ} (Num⟶ℕ b d o))
-- --     Surjective? zero d o = no reason
-- --         where   reason : ¬ Surjective (Num⟶ℕ 0 d o)
-- --                 reason surj = contradiction (right-inverse-of 1) {!   !}
-- --                     where
-- --                         from = Surjective.from surj
-- --                         right-inverse-of = Surjective.right-inverse-of surj
-- --     Surjective? (suc b) zero o = no {!   !}
-- --     Surjective? (suc b) (suc d) zero = {!   !}
-- --     Surjective? (suc b) (suc d) (suc o) with b ≤? d
-- --     Surjective? (suc b) (suc d) (suc o) | yes p = yes (record { from = ℕ⟶Num (suc b) (suc d) (suc o) ; right-inverse-of = λ x → {!   !} })
-- --     Surjective? (suc b) (suc d) (suc o) | no ¬p = no {!   !}
--
--     --
--     -- Surjective? : (b d o : ℕ) → Dec (Surjective {From = Num-Setoid b d o} {To = setoid ℕ} (Num⟶ℕ b d o))
--     -- Surjective? zero d o = no reason
--     --     where   reason : ¬ Surjective (Num⟶ℕ 0 d o)
--     --             reason surj = {!   !}
--     --     --         nono surj = contradiction {! ap  !} {!   !}
--     --     --             where
--     --     --                 from = Surjective.from surj
--     --     --                 ap = _⟨$⟩_ from     -- fromℕ
--     --     --                 cc = ap 1
--     --     --                 right-inverse-of = Surjective.right-inverse-of surj
--     -- Surjective? (suc b) d o = {!   !}
--     --
--     --
--     -- toℕ-surjective : ∀ {b d o} → {surj : True (Surjective? b d o)} → Surjective {From = Num-Setoid b d o} {To = setoid ℕ} (Num⟶ℕ b d o)
--     -- toℕ-surjective {zero}  {d} {o} {()}
--     -- toℕ-surjective {suc b} {d} {o} {surj} = record
--     --     { from = ℕ⟶Num (suc b) d o {surj}
--     --     ; right-inverse-of = {!   !} } -- (x : ℕ) → toℕ (fromℕ b d o x) ≡ x
--     --
--     --
--     -- ℕ⟶Num : ∀ b d o → {surj : True (Surjective? b d o)} → setoid ℕ ⟶ Num-Setoid b d o
--     -- ℕ⟶Num zero    d o {()}
--     -- ℕ⟶Num (suc b) d o {surj} = record
--     --     { _⟨$⟩_ = fromℕ (suc b) d o {surj}
--     --     ; cong = cong (toℕ ∘ fromℕ (suc b) d o {surj})
--     --     }
--     --
--     -- -- +1 : ∀ {b d o} → {surj : True (Surjective? b d o)} → Num b d o → Num b d o
--     -- -- +1 ∙ = {!   !}
--     -- -- +1 (x ∷ xs) = {!   !}
--     --
--     -- fromℕ : ∀ b d o → {surj : True (Surjective? b d o)} → ℕ → Num b d o
--     -- fromℕ zero d o {()} n
--     -- fromℕ (suc b) d o n = {!   !}
--
--     --
--     -- --
--     -- --
--     -- toℕ-surjective : ∀ {b d o} → Surjective {From = Num-Setoid b d o} {To = setoid ℕ} (Num⟶ℕ b d o)
--     -- toℕ-surjective {b} {d} {o} = record
--     --     { from = ℕ⟶Num b d o
--     --     ; right-inverse-of = λ x → {!   !} } -- (x : ℕ) → toℕ (fromℕ b d o x) ≡ x
--
--     -- ℕ⟶Num b d o = record
--         -- { _⟨$⟩_ = fromℕ b d o
--         -- ; cong = cong (toℕ ∘ fromℕ b d o)
--         -- }
--
--
--
-- --
-- --
-- --
-- -- IsSurjective : (b d o : ℕ) → Set
-- -- IsSurjective 0             _       _ = ⊥
-- -- IsSurjective (suc b)       0       _ = ⊥
-- -- IsSurjective (suc b)       (suc d) (suc (suc o)) = ⊥
-- -- IsSurjective 1             (suc d) 0 = d ≥ 1
-- -- IsSurjective (suc (suc b)) (suc d) 0 = suc b ≥ d
-- -- IsSurjective (suc b)       (suc d) 1 = d ≥ b
--
-- -- fromℕ : ∀ b d o → {cond : True (IsSurjective b d o)} → ℕ → Num b d o
-- -- fromℕ b d o x = ?
-- -- fromℕ : ∀ b d o → {cond : IsSurjective b d o} → ℕ → Num b d o
-- -- fromℕ 0             n       _             {()} x
-- -- fromℕ (suc b)       0       _             {()} x
-- -- fromℕ (suc b)       (suc d) (suc (suc o)) {()} x
-- -- -- starts from 0
-- -- fromℕ 1             1             0 {()} x
-- -- fromℕ 1             (suc (suc d)) 0 zero = ∙
-- -- fromℕ 1             (suc (suc d)) 0 (suc x) = s z ∷ fromℕ 1 (suc (suc d)) 0 {s≤s z≤n} x
-- -- fromℕ (suc (suc b)) (suc d)       0 x = {!   !}
-- -- -- starts from 1
-- -- fromℕ (suc b)       (suc d) 1 x = {!   !}
--
--
--
-- -- Num-DecTotalOrder : ∀ b d o → DecTotalOrder _ _ _
-- -- Num-DecTotalOrder b d o = record
-- --     { Carrier = Num b d o
-- --     ; _≈_ = _≋_
-- --     ; _≤_ = _≲_
-- --     ; isDecTotalOrder = record
-- --         { isTotalOrder = record
-- --             { isPartialOrder = record
-- --                 { isPreorder = record
-- --                     { isEquivalence = ≋-isEquivalence
-- --                     ; reflexive = IsPreorder.reflexive isPreorder
-- --                     ; trans = IsPreorder.trans isPreorder -- ≲-Transitive
-- --                     }
-- --                 ; antisym = IsPartialOrder.antisym isPartialOrder
-- --                 }
-- --             ; total = λ x y → IsTotalOrder.total isTotalOrder (toℕ x) (toℕ y) }
-- --         ; _≟_ = {!   !}
-- --         ; _≤?_ = {!   !}
-- --         }
-- --     }
-- --     where
-- --         open import Data.Nat.Properties.Extra
-- --
-- --         ≋-isEquivalence : ∀ {b d o} → IsEquivalence {A = Num b d o} _≋_
-- --         ≋-isEquivalence = record
-- --             { refl = λ {x} → refl
-- --             ; sym = sym
-- --             ; trans = trans
-- --             }
--
-- --
--
-- -- surjective : ∀ b d o → Dec (Surjective {From = record { Carrier = {!   !} ; _≈_ = {!   !} ; isEquivalence = {!   !} }} {To = {!   !}} {!   !})
-- -- surjective = {!   !}
--
-- --
-- -- -- digit+1 : ∀ {b n} → (x : Fin n) → Fin.toℕ x ≢ b → Fin n
-- -- -- digit+1 = {!   !}
-- -- -- ∀ {b} → (x : Fin (suc b)) → Fin.toℕ x ≢ b → Fin (suc b)
-- -- -- digit+1 {b} x ¬p = fromℕ≤ {digit-toℕ x} (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p))
-- --
-- --
-- --
-- -- -- 1+ : ∀ {b d o} → Num b d o → Num b d o
-- -- -- 1+ ∙ = {!   !}
-- -- -- 1+ (x ∷ xs) = {!   !}
-- -- -- 1+ ∙        = z ∷ ∙
-- -- -- 1+ {suc b} {zero}  (() ∷ xs)
-- -- -- 1+ {suc b} {suc d} (x ∷ xs) with full x b
-- -- -- 1+ {suc b} {suc d} (x ∷ xs) | yes p = z ∷ 1+ xs
-- -- -- 1+ {suc b} {suc d} (x ∷ xs) | no ¬p = {!   !}
-- --
-- --
-- --
-- --
-- -- -- Truncates the LSD (least significant digit 😜) down, and performs carrying
-- -- -- as much as possible.
-- -- normalize-LSD : ∀ {b d o} → Num b d o → Num b d o
-- -- normalize-LSD ∙ = ∙
-- -- normalize-LSD {zero} {n} {o} (x ∷ xs) = {!   !}
-- -- normalize-LSD {suc b} {n} {o} (x ∷ xs) with suc b ≤? n
-- -- normalize-LSD {suc b} (x ∷ xs) | yes p with Fin.toℕ x divMod (suc b)
-- -- normalize-LSD {suc b} (x ∷ xs) | yes p | result quotient remainder property div-eq mod-eq
-- --     = inject≤ remainder p ∷ {!   !}
-- -- normalize-LSD {suc b} (x ∷ xs) | no ¬p = x ∷ xs  -- base > # of digits
-- -- -- normalize-LSD {suc b} (x ∷ xs) with Fin.toℕ x divMod (suc b)
-- -- -- normalize-LSD {suc b} (x ∷ xs) | result quotient remainder property div-eq mod-eq
-- -- --     = {! remainder  !} ∷ {!   !}
-- --
-- -- -- base = 2
-- -- -- offseet = 0
-- -- -- n = 3
-- -- -- 0 1 2
-- --
-- --
-- --
-- --
-- -- -- 1 2 == 2 0
-- --
-- --
-- -- -- propositional equality of Num
-- -- _≋_ : ∀ {b d o} → Num b d o → Num b d o → Set
-- -- x ≋ y = toℕ x ≡ toℕ y
-- --
-- -- _≋?_ : ∀ {b d o} → Decidable {A = Num b d o} _≋_
-- -- _≋?_             ∙          ∙          = yes refl
-- -- _≋?_ {o = zero}  ∙          (  z ∷ ys) = {!   !}  -- digit is 0, can't decide yet
-- -- _≋?_ {o = zero}  ∙          (s x ∷ ys) = no (λ ())
-- -- _≋?_ {o = suc o} ∙          (  x ∷ ys) = no (λ ())
-- -- _≋?_ {o = zero}  (  z ∷ xs) ∙          = {!   !}  -- digit is 0, can't decide yet
-- -- _≋?_ {o = zero}  (s x ∷ xs) ∙          = no (λ ())
-- -- _≋?_ {o = suc o} (  x ∷ xs) ∙          = no (λ ())
-- -- _≋?_             (  x ∷ xs) (  y ∷ ys) with x F≟ y
-- -- _≋?_ {b} {n} {o} (  x ∷ xs) (  y ∷ ys) | yes p = {! xs ≋? ys  !}
-- -- _≋?_ {b} {n} {o} (  x ∷ xs) (  y ∷ ys) | no ¬p = {!   !}
-- --
-- --
-- --
-- -- -- (x ∷ xs) ≋? (y ∷ ys) | no ¬p | yes q = no {!   !}
-- -- -- (x ∷ xs) ≋? (y ∷ ys) | no ¬p | no ¬q = {!   !}
-- -- -- _≋?_ {b} {o} {n} (  x ∷ xs) (  y ∷ ys) | no ¬p = no (λ q → contradiction {! cancel-+-left   !} ¬p)
-- -- --     where   open import Data.Nat.Properties
-- -- -- _≋?_  = λ x y → {!   !}
-- --
-- -- -- _≋?_ {o = zero}  ∙          (  z ∷ ys) = {!   !}  -- digit is 0, can't decide yet
-- -- -- _≋?_ {o = zero}  ∙          (s x ∷ ys) = no (λ ())
-- -- -- _≋?_ {o = suc o} ∙          (  x ∷ ys) = no (λ ())
-- -- -- _≋?_ {o = zero}  (  z ∷ xs) ∙          = {!   !}  -- digit is 0, can't decide yet
-- -- -- _≋?_ {o = zero}  (s x ∷ xs) ∙          = no (λ ())
-- -- -- _≋?_ {o = suc o} (  x ∷ xs) ∙          = ?
-- -- -- _≋?_             (  x ∷ xs) (  y ∷ ys) with x F≟ y
-- -- -- _≋?_ {b} {n} {o} (  x ∷ xs) (  y ∷ ys) | yes p = {! xs ≋? ys  !}
-- -- -- _≋?_ {b} {n} {o} (  x ∷ xs) (  y ∷ ys) | no ¬p with xs ≋? ys
-- -- -- (x ∷ xs) ≋? (y ∷ ys) | no ¬p | yes q = no {!   !}
-- -- -- (x ∷ xs) ≋? (y ∷ ys) | no ¬p | no ¬q = {!   !}
-- -- -- _≋?_ {b} {o} {n} (  x ∷ xs) (  y ∷ ys) | no ¬p = no (λ q → contradiction {! cancel-+-left   !} ¬p)
-- -- --     where   open import Data.Nat.Properties
-- -- -- _≋?_  = λ x y → {!   !}
-- --
-- -- -- ≋-cong : ∀ {b d o a} (f : Num b d o → Num b d o) {x y} → x ≋ y → {!   !} ≋ {!   !}
-- -- -- ≋-cong f eq = {!   !}
-- --
-- --
-- -- -- ≋-Reflexive : ∀ {b d o} → Reflexive {_} {_} {Num b d o} _≋_
-- -- -- ≋-Reflexive {b} {o} {n} {∙}      = tt
-- -- -- ≋-Reflexive {b} {o} {n} {x ∷ xs} with x F≟ x
-- -- -- ≋-Reflexive {b} {o} {n} {x ∷ xs} | yes p = {!   !}
-- -- -- -- ≋-Reflexive {b} {o} {n} {x ∷ xs} | yes p = ≋-Reflexive {b} {o} {n} {xs}
-- -- -- ≋-Reflexive {b} {o} {n} {x ∷ xs} | no ¬p = contradiction refl ¬p
-- --
-- -- -- (∼ : A → A → Set ℓ) → Σ
-- -- --     ({x = a : A} {x = b : A} {y = c : A} → b ≡ c → a ~ b → a ~ c)
-- -- --     ({y = a : A} {x = b : A} {y = c : A} → b ≡ c → b ~ a → c ~ a)
-- --
-- -- -- _≋_ : ∀ {b d o} → Num b d o → Num b d o → Set
-- -- -- xs ≋ ys = toℕ xs ≡ toℕ ys
-- --
-- -- -- ≋-isEquivalence : ∀ {b d o} → IsEquivalence {_} {_} {Num b d o} _≋_
-- -- -- ≋-isEquivalence = record
-- -- --     { refl = λ {x} → refl
-- -- --     ; sym = sym
-- -- --     ; trans = trans
-- -- --     }
-- -- -- --
-- -- -- open import Function.Surjection
-- -- --
-- -- --
-- -- --
-- -- -- -- NumSetoid : ∀ b d o → Setoid _ _
-- -- -- -- NumSetoid b d o = record
-- -- -- --     { Carrier = Num b d o
-- -- -- --     ; _≈_ = λ x y → toℕ x ≡ toℕ y
-- -- -- --     ; isEquivalence = record
-- -- -- --         { refl = λ {x} → refl
-- -- -- --         ; sym = {!   !}
-- -- -- --         ; trans = {!   !}
-- -- -- --         } }
-- -- --
-- -- -- ℕSetoid : Setoid _ _
-- -- -- ℕSetoid = setoid ℕ
-- -- --
-- -- -- isSurjective : (b d o : ℕ) → Surjective {From = {!   !}} {To = ℕSetoid} {! toℕ  !}
-- -- -- isSurjective = {!   !}
