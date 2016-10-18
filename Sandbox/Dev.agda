module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
open import Data.Num.Incrementable
-- open import Data.Num.Continuous

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra

open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)

open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)
open import Data.Product
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import Function
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

-- Incrementable : ∀ {b d o} → (xs : Num b d o) → Set
-- Incrementable {b} {d} {o} xs = Σ[ xs' ∈ Num b d o ] ⟦ xs' ⟧ ≡ suc ⟦ xs ⟧

data Mx : {b d o : ℕ} (xs : Num b d o) → Set where
    mx : ∀ {b d o} {xs : Num b d o} → (max : Maximum xs) → Mx xs
data ¬Mx : {b d o : ℕ} (xs : Num b d o) → Set where
    ¬mx : ∀ {b d o} {xs : Num b d o} → (¬max : ¬ (Maximum xs)) → ¬Mx xs

⟦_⟧Mx : ∀ {b d o} {xs : Num b d o} → Mx xs → Maximum xs
⟦ mx max ⟧Mx = max
⟦_⟧¬Mx : ∀ {b d o} {xs : Num b d o} → ¬Mx xs → ¬ (Maximum xs)
⟦ ¬mx ¬max ⟧¬Mx = ¬max

next-number-NullBase' : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → ¬Mx xs
    → Num 0 (suc d) o
next-number-NullBase' {d} {o} xs ¬max with NullBase-view d o
next-number-NullBase' xs       ¬max | AllZeros = contradiction (AllZeros-Maximum xs) ⟦ ¬max ⟧¬Mx
next-number-NullBase' xs       ¬max | Others bound with Greatest? (lsd xs)
next-number-NullBase' xs       ¬max | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ⟦ ¬max ⟧¬Mx
next-number-NullBase' (x ∙   ) ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∙
next-number-NullBase' (x ∷ xs) ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∷ xs


next-number-suc-NullBase : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬m : ¬Mx xs)
    → ⟦ next-number-NullBase' xs ¬m ⟧ ≡ suc ⟦ xs ⟧
next-number-suc-NullBase {d} {o} xs ¬max with NullBase-view d o
next-number-suc-NullBase {_} {_} xs       ¬max | AllZeros = contradiction (AllZeros-Maximum xs) ⟦ ¬max ⟧¬Mx
next-number-suc-NullBase {d} {o} xs       ¬max | Others bound with Greatest? (lsd xs)
next-number-suc-NullBase {d} {o} xs       ¬max | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ⟦ ¬max ⟧¬Mx
next-number-suc-NullBase {d} {o} (x ∙)    ¬max | Others bound | no ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o
    ≡⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Fin.toℕ x + o)
    ∎
next-number-suc-NullBase {d} {o} (x ∷ xs) ¬max | Others bound | no ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * zero
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * zero) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Fin.toℕ x + o + ⟦ xs ⟧ * zero)
    ∎

Incrementable-NullBase :  ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬m : ¬Mx xs)
    → Incrementable xs
Incrementable-NullBase {d} {o} xs ¬max with NullBase-view d o
Incrementable-NullBase xs         ¬max | AllZeros = contradiction (AllZeros-Maximum xs) ⟦ ¬max ⟧¬Mx
Incrementable-NullBase xs         ¬max | Others bound with Greatest? (lsd xs)
Incrementable-NullBase xs         ¬max | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ⟦ ¬max ⟧¬Mx
Incrementable-NullBase xs         ¬max | Others bound | no ¬greatest = (next-number-NullBase' xs ¬max) , (next-number-suc-NullBase xs ¬max)


-----------------------------
-----------------------------
-----------------------------
-----------------------------

data IncrementableCond : (b d o : ℕ) (xs : Num b d o) → Set where
    NullBase : ∀ {d o}
        → {xs : Num 0 (suc d) o}
        → (¬mx : ¬Mx xs)
        → IncrementableCond 0 (suc d) o xs
    Others-Abundant : ∀ {b d o}
        → {xs : Num (suc b) (suc d) o}
        → (¬max : ¬ (Maximum xs))
        → (abundant : Abundant (suc b) (suc d) o)
        → IncrementableCond (suc b) (suc d) o xs
    Others-Sparse : ∀ {b d o}
        → {xs : Num (suc b) (suc d) o}
        → (¬max : ¬ (Maximum xs))
        → (¬greatest : ¬ (Greatest (lsd xs)))
        → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
        → IncrementableCond (suc b) (suc d) o xs

    -- Others-Sparse-Single : ∀ {b d o}
    --     → (x : Digit (suc d))
    --     → (¬greatest : ¬ (Greatest x))
    --     → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
    --     → IncrementableCond (suc b) (suc d) o
    -- Others-Sparse : ∀ {b d o}
    --     → (x : Digit (suc d))
    --     → (xs : Num (suc b) (suc d) o)
    --     → (¬max : ¬ (Maximum xs))
    --     → (¬greatest : ¬ (Greatest x))
    --     → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
    --     → IncrementableCond (suc b) (suc d) o

data NonIncrementableCond : (b d o : ℕ) (xs : Num b d o) → Set where
    Max : ∀ {b d o}
        → {xs : Num b d o}
        → (max : Maximum xs)
        → NonIncrementableCond b d o xs
    Others : ∀ {b d o}
        → {xs : Num (suc b) (suc d) o}
        → (¬max : ¬ (Maximum xs))
        → (greatest : Greatest (lsd xs))
        → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
        → NonIncrementableCond (suc b) (suc d) o xs

    -- Others-Single : ∀ {b d o}
    --     → (x : Digit (suc d))
    --     → (greatest : Greatest x)
    --     → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
    --     → NonIncrementableCond (suc b) (suc d) o
    -- Others : ∀ {b d o}
    --     → (x : Digit (suc d))
    --     → (xs : Num (suc b) (suc d) o)
    --     → (¬max : ¬ (Maximum xs))
    --     → (greatest : Greatest x)
    --     → (¬abundant : ¬ (Abundant (suc b) (suc d) o))
    --     → NonIncrementableCond (suc b) (suc d) o



data IncrementableView : (b d o : ℕ) (xs : Num b d o) → Set where
    IsIncrementable : ∀ {b d o} {xs : Num b d o}
        → IncrementableCond b d o xs
        → IncrementableView b d o xs
    IsntIncrementable : ∀ {b d o} {xs : Num b d o}
        → NonIncrementableCond b d o xs
        → IncrementableView b d o xs

incrementableView : ∀ {b d o}
    → (xs : Num b d o)
    → IncrementableView b d o xs
incrementableView xs with Maximum? xs
incrementableView xs | yes max = IsntIncrementable (Max max)
incrementableView {b} {d} {o} xs | no ¬max with boundedView b d o
incrementableView xs | no ¬max | IsBounded (NullBase d o) = IsIncrementable (NullBase (¬mx ¬max))
incrementableView xs | no ¬max | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) with Abundant? (suc b) (suc d) o
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) | yes abundant = IsIncrementable (Others-Abundant ¬max abundant)
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) | no ¬abundant with Greatest? (lsd xs)
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) | no ¬abundant | yes greatest = IsntIncrementable (Others ¬max greatest ¬abundant)
incrementableView xs | no ¬max | IsntBounded (Others b d o d+o≥2) | no ¬abundant | no ¬greatest = IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant)
incrementableView xs | no ¬max | IsntBounded (NoDigits b o) = NoDigits-explode xs

Incrementable? : ∀ {b d o}
    → (xs : Num b d o)
    → Dec (Incrementable xs)
Incrementable? xs with incrementableView xs
Incrementable? xs | IsIncrementable (NullBase ¬m) = yes ((next-number-NullBase' xs ¬m) , (next-number-suc-NullBase xs ¬m))
 -- = yes (Incrementable-NullBase xs ¬max)
Incrementable? xs | IsIncrementable (Others-Abundant ¬max abundant) = yes {!   !}
Incrementable? xs | IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant) = yes {!   !}
Incrementable? xs | IsntIncrementable (Max max) = no (Maximum⇒¬Incrementable xs max)
Incrementable? xs | IsntIncrementable (Others ¬max greatest ¬abundant) = {!   !}

increment :  ∀ {b d o}
    → (xs : Num b d o)
    → (incr : True (Incrementable? xs))
    → Num b d o
increment xs incr = proj₁ (toWitness incr)


increment-next-number-NullBase : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬m : ¬Mx xs)
    → (incr : True (Incrementable? xs))
    → increment xs incr ≡ next-number-NullBase' xs ¬m
increment-next-number-NullBase xs ¬m incr with incrementableView xs
increment-next-number-NullBase xs ¬m incr | IsIncrementable (NullBase ¬m') = refl
increment-next-number-NullBase xs ¬m incr | IsntIncrementable x = {!   !}

-- increment :  ∀ {b d o}
--     → (xs : Num b d o)
--     → Incrementable xs
--     → Num b d o
-- increment xs incr with incrementableView xs
-- increment xs incr | IsIncrementable (NullBase ¬max) = proj₁ incr
-- increment xs incr | IsIncrementable (Others-Abundant ¬max abundant) = {!   !}
-- increment xs incr | IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant) = {!   !}
-- increment xs incr | IsntIncrementable (Max max) = {!   !}
-- increment xs incr | IsntIncrementable (Others ¬max greatest ¬abundant) = {!   !}

-- increment-next-number : ∀ {b d o}
--     → (xs : Num b d o)
--     → (¬m : ¬Mx xs)
--     → (incr : True (Incrementable? xs))
--     → proj₁ (toWitness incr) ≡ next-number xs ¬max
-- increment-next-number xs ¬max incr with incrementableView xs
-- increment-next-number {_} {suc d} {o} xs ¬max incr | IsIncrementable (NullBase ¬m) = refl
    -- begin
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ∎
-- increment-next-number {_} {suc d} {o} xs ¬max₁ incr | IsIncrementable (NullBase ¬max) with boundedView 0 (suc d) o
-- increment-next-number {_} {suc .d} xs ¬max₁ incr | IsIncrementable (NullBase ¬max) | IsBounded (NullBase d o) = {!   !}
-- -- increment-next-number {_} {suc .d} xs ¬max₁ incr | IsIncrementable (NullBase ¬max) | IsBounded (NullBase d o) with NullBase-view d o
-- -- increment-next-number {_} {suc .0} xs ¬max₁ incr | IsIncrementable (NullBase ¬max) | IsBounded (NullBase .0 .0) | AllZeros = {!   !}
-- -- increment-next-number {_} {suc .d} xs ¬max₁ incr | IsIncrementable (NullBase ¬max) | IsBounded (NullBase d o) | Others bound with Greatest? (lsd xs)
-- -- increment-next-number {_} {suc .d} xs ¬max₁ incr | IsIncrementable (NullBase ¬max) | IsBounded (NullBase d o) | Others bound | yes p = {!   !}
-- -- increment-next-number {_} {suc .d} xs ¬max₁ incr | IsIncrementable (NullBase ¬max) | IsBounded (NullBase d o) | Others bound | no ¬p = {!   !}
-- increment-next-number {_} {suc d} xs ¬max₁ incr | IsIncrementable (NullBase ¬max) | IsntBounded cond = {!   !}
    -- begin
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ∎
-- increment-next-number xs ¬max₁ incr | IsIncrementable (Others-Abundant ¬max abundant) = {!   !}
-- increment-next-number xs ¬max₁ incr | IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant) = {!   !}
-- increment-next-number xs ¬max incr | IsntIncrementable (Max max) = {!   !}
-- increment-next-number xs ¬max₁ incr | IsntIncrementable (Others ¬max greatest ¬abundant) = {!   !}

-----------------------------
-----------------------------
-----------------------------
-----------------------------

-- Incrementable? : ∀ {b d o}
--     → (xs : Num b d o)
--     → Dec (Incrementable xs)
-- Incrementable? xs with Maximum? xs
-- Incrementable? xs | yes max = no (Maximum⇒¬Incrementable xs max)
-- Incrementable? {b} {d} {o} xs | no ¬max with boundedView b d o
-- Incrementable? xs | no ¬max | IsBounded (NullBase d o) = yes (Incrementable-NullBase xs ¬max)
-- Incrementable? xs | no ¬max | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
-- Incrementable? xs | no ¬max | IsntBounded (Others b d o d+o≥2) with Abundant? (suc b) (suc d) o
-- Incrementable? xs | no ¬max | IsntBounded (Others b d o d+o≥2) | yes abundant = {!   !} -- yes (Incrementable-Others-Abundant xs ¬max d+o≥2 abundant)
-- Incrementable? xs | no ¬max | IsntBounded (Others b d o d+o≥2) | no ¬abundant = {!    !}
-- Incrementable? xs | no ¬max | IsntBounded (NoDigits b o) = NoDigits-explode xs
--
-- increment : ∀ {b d o}
--     → (xs : Num b d o)
--     → Incrementable xs
--     → Num b d o
-- increment xs incr with Maximum? xs
-- increment xs incr | yes max = contradiction incr (Maximum⇒¬Incrementable xs max)
-- increment {b} {d} {o} xs incr | no ¬max with boundedView b d o
-- increment xs (next , proof) | no ¬max | IsBounded (NullBase d o) = next
-- increment xs (next , proof) | no ¬max | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
-- increment xs incr | no ¬max | IsntBounded (Others b d o d+o≥2) with Abundant? (suc b) (suc d) o
-- increment xs incr | no ¬max | IsntBounded (Others b d o d+o≥2) | yes abundant = {!   !}
-- increment xs incr | no ¬max | IsntBounded (Others b d o d+o≥2) | no ¬abundant = {!   !}
-- increment xs incr | no ¬max | IsntBounded (NoDigits b o) = NoDigits-explode xs
--
-- increment-next-number : ∀ {b d o}
--     → (xs : Num b d o)
--     → (¬max : ¬ (Maximum xs))
--     → (incr : Incrementable xs)
--     → increment xs incr ≡ next-number xs ¬max
-- increment-next-number {b} {d} {o} xs ¬max incr with Maximum? xs
-- increment-next-number xs ¬max incr | yes max = contradiction max ¬max
-- increment-next-number {b} {d} {o} xs ¬max incr | no _ with boundedView b d o
-- increment-next-number xs ¬max (proj₁ , proj₂) | no ¬p | IsBounded (NullBase d o) =
--     begin
--         {!   !}
--     ≡⟨ refl ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         next-number-NullBase xs ¬max
--     ∎
-- increment-next-number xs ¬max incr | no ¬p | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
-- increment-next-number xs ¬max incr | no ¬p | IsntBounded (Others b d o d+o≥2) = {!   !}
-- increment-next-number xs ¬max incr | no ¬p | IsntBounded (NoDigits b o) = {!   !}


-- increment-next-number {b} {d} {o} xs ¬max incr with boundedView b d o
-- increment-next-number xs ¬max incr | IsBounded (NullBase d o) = {!   !}
-- increment-next-number xs ¬max incr | IsBounded (AllZeros b) = {!   !}
-- increment-next-number xs ¬max incr | IsntBounded (Others b d o d+o≥2) = {!   !}
-- increment-next-number xs ¬max incr | IsntBounded (NoDigits b o) = {!   !}

-- increment-next-number-NullBase : ∀ {d o}
--     → (xs : Num 0 (suc d) o)
--     → (¬max : ¬ (Maximum xs))
--     → (incr : Incrementable xs)
--     → increment xs incr ≡ next-number-NullBase xs ¬max
-- increment-next-number-NullBase {d} {o} xs ¬max incr with Maximum? xs
-- increment-next-number-NullBase xs ¬max incr | yes p = {!   !}
-- increment-next-number-NullBase {d} {o} xs ¬max (next , prop) | no ¬p with boundedView 0 (suc d) o
-- increment-next-number-NullBase xs ¬max (next , prop) | no ¬p | IsBounded (NullBase d o) = {!   !}
-- increment-next-number-NullBase xs ¬max (next , prop) | no ¬p | IsntBounded cond = {!   !}
-- increment-next-number-NullBase {d} {o} xs ¬max incr with NullBase-view d o
-- increment-next-number-NullBase xs ¬max incr | AllZeros = AllZeros-explode xs ¬max
-- increment-next-number-NullBase xs ¬max incr | Others bound with Greatest? (lsd xs)
-- increment-next-number-NullBase xs ¬max incr | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ¬max
-- increment-next-number-NullBase xs ¬max (proj₁ , proj₂) | Others bound | no ¬greatest = {!   !}


-- start
--     {!   !}
-- ≈⟨ {!   !} ⟩
--     {!   !}
-- ≈⟨ {!   !} ⟩
--     {!   !}
-- ≈⟨ {!   !} ⟩
--     {!   !}
-- □

-- begin
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ∎
-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- □
