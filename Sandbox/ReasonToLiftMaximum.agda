module Sandbox.ReasonToLiftMaximum where
module Sandbox.ReasonToLiftMaximum where

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

next-number-suc-NullBase : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ next-number-NullBase xs ¬max ⟧ ≡ suc ⟦ xs ⟧
next-number-suc-NullBase {d} {o} xs ¬max with NullBase-view d o
next-number-suc-NullBase {_} {_} xs       ¬max | AllZeros = contradiction (AllZeros-Maximum xs) ¬max
next-number-suc-NullBase {d} {o} xs       ¬max | Others bound with Greatest? (lsd xs)
next-number-suc-NullBase {d} {o} xs       ¬max | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ¬max
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
    → (¬max : ¬ (Maximum xs))
    → Incrementable xs
Incrementable-NullBase {d} {o} xs ¬max with NullBase-view d o
Incrementable-NullBase xs         ¬max | AllZeros = contradiction (AllZeros-Maximum xs) ¬max
Incrementable-NullBase xs         ¬max | Others bound with Greatest? (lsd xs)
Incrementable-NullBase xs         ¬max | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ¬max
Incrementable-NullBase xs         ¬max | Others bound | no ¬greatest = (next-number-NullBase xs ¬max) , (next-number-suc-NullBase xs ¬max)


data IncrementableCond : (b d o : ℕ) (xs : Num b d o) → Set where
    NullBase : ∀ {d o}
        → {xs : Num 0 (suc d) o}
        → (¬max : ¬ (Maximum xs))
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
incrementableView xs | no ¬max | IsBounded (NullBase d o) = IsIncrementable (NullBase ¬max)
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
Incrementable? xs | IsIncrementable (NullBase ¬max) = yes (Incrementable-NullBase xs ¬max)
Incrementable? xs | IsIncrementable (Others-Abundant ¬max abundant) = yes {!   !}
Incrementable? xs | IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant) = yes {!   !}
Incrementable? xs | IsntIncrementable (Max max) = no (Maximum⇒¬Incrementable xs max)
Incrementable? xs | IsntIncrementable (Others ¬max greatest ¬abundant) = {!   !}

increment-next-number : ∀ {b d o}
    → (xs : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → (incr : True (Incrementable? xs))
    → proj₁ (toWitness incr) ≡ next-number xs ¬max
increment-next-number xs ¬max incr with incrementableView xs
increment-next-number {_} {suc d} {o} xs ¬max₁ incr | IsIncrementable (NullBase ¬max) = {!   !}
increment-next-number xs ¬max₁ incr | IsIncrementable (Others-Abundant ¬max abundant) = {!   !}
increment-next-number xs ¬max₁ incr | IsIncrementable (Others-Sparse ¬max ¬greatest ¬abundant) = {!   !}
increment-next-number xs ¬max incr | IsntIncrementable (Max max) = {!   !}
increment-next-number xs ¬max₁ incr | IsntIncrementable (Others ¬max greatest ¬abundant) = {!   !}
