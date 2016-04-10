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
    WithZero : ∀ {b d} → (b≥1 : b ≥ 1) → (d≥2 : d ≥ 2) → (b≤d : b ≤ d) → SurjectionView b d 0
    Zeroless : ∀ {b d} → (b≥1 : b ≥ 1) → (d≥1 : d ≥ 1) → (b≤d : b ≤ d) → SurjectionView b d 1
    Spurious  : ∀ {b d o} → SurjectionView b d o

surjectionView : (b d o : ℕ) → SurjectionView b d o
-- # base = 0
surjectionView 0             d             o = Spurious
-- # base ≥ 1
surjectionView (suc b)       0             o = Spurious
--      # starts from 0 (offset = 0)
surjectionView (suc b)       (suc d)       0 with suc b ≤? suc d
surjectionView (suc b)       1             0 | yes p = Spurious     -- Unary number that possesses only 1 digit: { 0 }
surjectionView 1             (suc (suc d)) 0 | yes p = WithZero (s≤s z≤n) (s≤s (s≤s z≤n)) p
surjectionView (suc (suc b)) (suc (suc d)) 0 | yes p = WithZero (s≤s z≤n) (≤-trans (s≤s (s≤s z≤n)) p) p
    where   open import Data.Nat.Properties.Extra using (≤-trans)
surjectionView (suc b)       (suc d)       0 | no ¬p = Spurious         -- not enough digits
--      # starts from 1 (offset = 1)
surjectionView (suc b)       (suc d)       1 with suc b ≤? suc d
surjectionView (suc b)       (suc d)       1 | yes p = Zeroless (s≤s z≤n) (s≤s z≤n) p
surjectionView (suc b)       (suc d)       1 | no ¬p = Spurious         -- not enough digits

surjectionView (suc b)       (suc d)       (suc (suc o)) = Spurious     -- offset ≥ 2

notSpurious? : ∀ {b d o} → (view : SurjectionView b d o) → Dec (view ≢ Spurious)
notSpurious? (WithZero b≥1 d≥2 b≤d) = yes (λ ())
notSpurious? (Zeroless b≥1 d≥1 b≤d) = yes (λ ())
notSpurious? Spurious       = no (λ x → contradiction refl x)

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

digit+1-b : ∀ {b d} → (x : Digit d)
    → b ≥ 1 → suc (Fin.toℕ x) ≡ d
    → Fin d
digit+1-b {b} {d} x b≥1 p =
    fromℕ≤ {suc (Fin.toℕ x) ∸ b} (digit+1-b-lemma x b≥1 p)

1+ : ∀ {b d o}
    → (view : SurjectionView b d o)
    → {notSpurious : True (notSpurious? view)}
    → Num b d o
    → Num b d o
1+ (WithZero b≥1 d≥2 b≤d) ∙        = fromℕ≤ {1} d≥2 ∷ ∙     -- 0 ⇒ 1
1+ (WithZero b≥1 d≥2 b≤d) (x ∷ xs) with full x
1+ (WithZero b≥1 d≥2 b≤d) (x ∷ xs) | yes p =
    digit+1-b x b≥1 p ∷ 1+ (WithZero b≥1 d≥2 b≤d) xs         -- n ⇒ n + 1 - b
1+ (WithZero b≥1 d≥2 b≤d) (x ∷ xs) | no ¬p =
    fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p) ∷ xs   -- 8 ⇒ 9
1+ (Zeroless b≥1 d≥1 b≤d) ∙        = fromℕ≤ {0} d≥1 ∷ ∙     -- ∙ ⇒ 1
1+ (Zeroless b≥1 d≥1 b≤d) (x ∷ xs) with full x
1+ (Zeroless b≥1 d≥1 b≤d) (x ∷ xs) | yes p =
    digit+1-b x b≥1 p ∷ 1+ (Zeroless b≥1 d≥1 b≤d) xs         -- n ⇒ n + 1 - b
1+ (Zeroless b≥1 d≥1 b≤d) (x ∷ xs) | no ¬p =
    fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬p) ∷ xs   -- 8 ⇒ 9
1+ Spurious          {()} xs


fromℕ : ∀ {b d o}
    → (view : SurjectionView b d o)
    → {notSpurious : True (notSpurious? view)}
    → ℕ
    → Num b d o
fromℕ (WithZero b≥1 d≥2 b≤d) zero = ∙
fromℕ (WithZero b≥1 d≥2 b≤d) (suc n) = 1+ (WithZero b≥1 d≥2 b≤d) (fromℕ (WithZero b≥1 d≥2 b≤d) n)
fromℕ (Zeroless b≥1 d≥1 b≤d) zero = ∙
fromℕ (Zeroless b≥1 d≥1 b≤d) (suc n) = 1+ (Zeroless b≥1 d≥1 b≤d) (fromℕ (Zeroless b≥1 d≥1 b≤d) n)
fromℕ Spurious {()} n

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
