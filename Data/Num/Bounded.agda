module Data.Num.Bounded where

open import Data.Num.Core

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

------------------------------------------------------------------------
-- Views

data BoundedView : ℕ → ℕ → ℕ → Set where
    NullBase    : ∀   d o                           → BoundedView 0       (suc d) o
    NoDigits    : ∀ b o                             → BoundedView b       0       o
    AllZeros    : ∀ b                               → BoundedView (suc b) 1       0
    Others      : ∀ b d o → (d+o≥2 : suc d + o ≥ 2) → BoundedView (suc b) (suc d) o

boundedView : ∀ b d o → BoundedView b d o
boundedView b       zero          o       = NoDigits b o
boundedView zero    (suc d)       o       = NullBase d o
boundedView (suc b) (suc zero)    zero    = AllZeros b
boundedView (suc b) (suc zero)    (suc o) = Others b zero (suc o) (s≤s (s≤s z≤n))
boundedView (suc b) (suc (suc d)) o       = Others b (suc d) o (s≤s (s≤s z≤n))
------------------------------------------------------------------------
-- Relations between Conditions and Predicates

NullBase-toℕ : ∀ {d o}
    → (x : Digit d)
    → (xs : Num 0 d o)
    → ⟦ x ∷ xs ⟧ ≡ Digit-toℕ x o
NullBase-toℕ {d} {o} x xs =
    begin
        Digit-toℕ x o + ⟦ xs ⟧ * 0
    ≡⟨ cong (λ w → Digit-toℕ x o + w) (*-right-zero ⟦ xs ⟧) ⟩
        Digit-toℕ x o + 0
    ≡⟨ +-right-identity (Digit-toℕ x o) ⟩
        Digit-toℕ x o
    ∎

NullBase-Maximum : ∀ {d} {o}
    → (xs : Num 0 (suc d) o)
    → Greatest (lsd xs)
    → Maximum xs
NullBase-Maximum {_} {o} (x ∙) greatest (y ∙) = greatest-of-all o x y greatest
NullBase-Maximum {_} {o} (x ∙) greatest (y ∷ ys) =
    start
        Fin.toℕ y + o + ⟦ ys ⟧ * 0
    ≈⟨ NullBase-toℕ y ys ⟩
        Fin.toℕ y + o
    ≤⟨ greatest-of-all o x y greatest ⟩
        Fin.toℕ x + o
    □
NullBase-Maximum {_} {o} (x ∷ xs) greatest (y ∙) =
    start
        Fin.toℕ y + o
    ≤⟨ greatest-of-all o x y greatest ⟩
        Fin.toℕ x + o
    ≈⟨ sym (NullBase-toℕ x xs) ⟩
        Fin.toℕ x + o + ⟦ xs ⟧ * 0
    □
NullBase-Maximum {_} {o} (x ∷ xs) greatest (y ∷ ys) =
    start
        ⟦ y ∷ ys ⟧
    ≈⟨ NullBase-toℕ y ys ⟩
        Fin.toℕ y + o
    ≤⟨ greatest-of-all o x y greatest ⟩
        Fin.toℕ x + o
    ≈⟨ sym (NullBase-toℕ x xs) ⟩
        ⟦ x ∷ xs ⟧
    □

AllZeros-toℕ : ∀ {b} → (xs : Num b 1 0) → ⟦ xs ⟧ ≡ 0
AllZeros-toℕ     (z    ∙   ) = refl
AllZeros-toℕ     (s () ∙   )
AllZeros-toℕ {b} (z    ∷ xs) = cong (λ w → w * b) (AllZeros-toℕ xs)
AllZeros-toℕ     (s () ∷ xs)

AllZeros-Maximum : ∀ {b} → (xs : Num b 1 0) → Maximum xs
AllZeros-Maximum xs ys = reflexive $
    begin
        ⟦ ys ⟧
    ≡⟨ AllZeros-toℕ ys ⟩
        zero
    ≡⟨ sym (AllZeros-toℕ xs) ⟩
        ⟦ xs ⟧
    ∎

Others-¬Bounded : ∀ b d o → d + o ≥ 1 → ¬ (Bounded (suc b) (suc d) o)
Others-¬Bounded b d o d+o≥1 (xs , claim) = contradiction p ¬p
    where
        p : ⟦ xs ⟧ ≥ ⟦ greatest-digit d ∷ xs ⟧
        p = claim (greatest-digit d ∷ xs)
        ¬p : ⟦ xs ⟧ ≱ ⟦ greatest-digit d ∷ xs ⟧
        ¬p = <⇒≱ $
            start
                suc ⟦ xs ⟧
            ≈⟨ cong suc (sym (*-right-identity ⟦ xs ⟧)) ⟩
                suc (⟦ xs ⟧ * 1)
            ≤⟨ s≤s (n*-mono ⟦ xs ⟧ (s≤s z≤n)) ⟩
                suc (⟦ xs ⟧ * suc b)
            ≤⟨ +n-mono (⟦ xs ⟧ * suc b) d+o≥1 ⟩
                d + o + ⟦ xs ⟧ * suc b
            ≈⟨ cong
                (λ w → w + ⟦ xs ⟧ * suc b)
                (sym (toℕ-greatest (Fin.fromℕ d) (greatest-digit-is-the-Greatest d)))
            ⟩
                ⟦ greatest-digit d ∷ xs ⟧
            □

NoDigits-explode : ∀ {b o a} {Whatever : Set a}
    → (xs : Num b 0 o)
    → Whatever
NoDigits-explode (() ∙   )
NoDigits-explode (() ∷ xs)

AllZeros-explode : ∀ {a} {Whatever : Set a} {b}
    → (xs : Num b 1 0)
    → ¬ (Maximum xs)
    → Whatever
AllZeros-explode xs ¬max = contradiction (AllZeros-Maximum xs) ¬max

NoDigits-¬Bounded : ∀ b o → ¬ (Bounded b 0 o)
NoDigits-¬Bounded b o (xs , claim) = NoDigits-explode xs

Bounded? : ∀ b d o → Dec (Bounded b d o)
Bounded? b d o with boundedView b d o
Bounded? .0       .(suc d) o  | NullBase d .o
    = yes ((greatest-digit d ∙) , (NullBase-Maximum (greatest-digit d ∙) (greatest-digit-is-the-Greatest d)))
Bounded? b        .0       o  | NoDigits .b .o
    = no (NoDigits-¬Bounded b o)
Bounded? .(suc b) .1       .0 | AllZeros b
    = yes ((z ∙) , (AllZeros-Maximum (z ∙)))
Bounded? .(suc b) .(suc d) o  | Others b d .o d+o≥2
    = no (Others-¬Bounded b d o (≤-pred d+o≥2))



--------------------------------------------------------------------------------
-- Misc

Maximum⇒Bounded : ∀ {b d o}
    → (xs : Num b d o)
    → Maximum xs
    → Bounded b d o
Maximum⇒Bounded xs max = xs , max

-- contraposition of Maximum⇒Bounded
¬Bounded⇒¬Maximum : ∀ {b d o}
    → (xs : Num b d o)
    → ¬ (Bounded b d o)
    → ¬ (Maximum xs)
¬Bounded⇒¬Maximum xs = contraposition (Maximum⇒Bounded xs)

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
