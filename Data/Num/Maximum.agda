module Data.Num.Maximum where

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

Maximum : ∀ {b d o} → (xs : Numeral b d o) → Set
Maximum {b} {d} {o} xs = (ys : Numeral b d o) → ⟦ xs ⟧ ≥ ⟦ ys ⟧

-- Maximum-unique : ∀ {b d o}
--     → (max xs : Numeral b d o)
--     → Maximum max
--     → Maximum xs
--     → ⟦ max ⟧ ≡ ⟦ xs ⟧
-- Maximum-unique max xs max-max xs-max = IsPartialOrder.antisym isPartialOrder
--     (xs-max max)
--     (max-max xs)

Maximum-NullBase-Greatest : ∀ {d} {o}
    → (xs : Numeral 0 (suc d) o)
    → Greatest (lsd xs)
    → Maximum xs
Maximum-NullBase-Greatest {_} {o} (x ∙) greatest (y ∙) =
    greatest-of-all o x y greatest
Maximum-NullBase-Greatest {_} {o} (x ∙) greatest (y ∷ ys) =
    start
        Fin.toℕ y + o + ⟦ ys ⟧ * 0
    ≈⟨ toℕ-NullBase y ys ⟩
        Fin.toℕ y + o
    ≤⟨ greatest-of-all o x y greatest ⟩
        Fin.toℕ x + o
    □
Maximum-NullBase-Greatest {_} {o} (x ∷ xs) greatest (y ∙) =
    start
        Fin.toℕ y + o
    ≤⟨ greatest-of-all o x y greatest ⟩
        Fin.toℕ x + o
    ≈⟨ sym (toℕ-NullBase x xs) ⟩
        Fin.toℕ x + o + ⟦ xs ⟧ * 0
    □
Maximum-NullBase-Greatest {_} {o} (x ∷ xs) greatest (y ∷ ys) =
    start
        ⟦ y ∷ ys ⟧
    ≈⟨ toℕ-NullBase y ys ⟩
        Fin.toℕ y + o
    ≤⟨ greatest-of-all o x y greatest ⟩
        Fin.toℕ x + o
    ≈⟨ sym (toℕ-NullBase x xs) ⟩
        ⟦ x ∷ xs ⟧
    □

Maximum⇒Greatest-LSD : ∀ {b} {d} {o}
    → (xs : Numeral b d o)
    → Maximum xs
    → Greatest (lsd xs)
Maximum⇒Greatest-LSD xs max with Greatest? (lsd xs)
Maximum⇒Greatest-LSD xs max | yes greatest = greatest
Maximum⇒Greatest-LSD {b} {zero}      xs       max | no ¬greatest = NoDigits-explode xs
Maximum⇒Greatest-LSD {b} {suc d} {o} (x ∙)    max | no ¬greatest
    = contradiction p ¬p
    where
        ys : Numeral b (suc d) o
        ys = greatest-digit d ∙

        p : Digit-toℕ x o ≥ ⟦ ys ⟧
        p = max ys

        ¬p : Digit-toℕ x o ≱ ⟦ ys ⟧
        ¬p = <⇒≱ $
            start
                suc (Digit-toℕ x o)
            ≤⟨ +n-mono o (≤-pred (≤∧≢⇒< (bounded x) ¬greatest)) ⟩
                d + o
            ≈⟨ sym (greatest-digit-toℕ (Fin.fromℕ d) (greatest-digit-is-the-Greatest d)) ⟩
                Digit-toℕ (greatest-digit d) o
            ≈⟨ refl ⟩
                ⟦ ys ⟧
            □
Maximum⇒Greatest-LSD {b} {suc d} {o} (x ∷ xs) max | no ¬greatest
    = contradiction p ¬p
    where
        ys : Numeral b (suc d) o
        ys = greatest-digit d ∷ xs

        p : ⟦ x ∷ xs ⟧ ≥ ⟦ ys ⟧
        p = max ys

        ¬p : ⟦ x ∷ xs ⟧ ≱ ⟦ ys ⟧
        ¬p = <⇒≱ $ +n-mono (⟦ xs ⟧ * b) $
            start
                suc (Digit-toℕ x o)
            ≤⟨ +n-mono o (≤-pred (≤∧≢⇒< (bounded x) ¬greatest)) ⟩
                d + o
            ≈⟨ sym (greatest-digit-toℕ (Fin.fromℕ d) (greatest-digit-is-the-Greatest d)) ⟩
                (Digit-toℕ (greatest-digit d) o)
            □

Maximum-NullBase : ∀ {d} {o}
    → (xs : Numeral 0 (suc d) o)
    → Dec (Maximum xs)
Maximum-NullBase xs with Greatest? (lsd xs)
Maximum-NullBase xs | yes greatest = yes (Maximum-NullBase-Greatest xs greatest)
Maximum-NullBase xs | no ¬greatest = no (contraposition (Maximum⇒Greatest-LSD xs) ¬greatest)

Maximum-AllZeros : ∀ {b} → (xs : Numeral b 1 0) → Maximum xs
Maximum-AllZeros xs ys = reflexive $
    begin
        ⟦ ys ⟧
    ≡⟨ toℕ-AllZeros ys ⟩
        zero
    ≡⟨ sym (toℕ-AllZeros xs) ⟩
        ⟦ xs ⟧
    ∎

Maximum-Proper : ∀ {b d o}
    → (xs : Numeral (suc b) (suc d) o)
    → (proper : 2 ≤ suc (d + o))
    → ¬ (Maximum xs)
Maximum-Proper {b} {d} {o} xs proper claim = contradiction p ¬p
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
            ≤⟨ +n-mono (⟦ xs ⟧ * suc b) (≤-pred proper) ⟩
                d + o + ⟦ xs ⟧ * suc b
            ≈⟨ cong
                (λ w → w + ⟦ xs ⟧ * suc b)
                (sym (greatest-digit-toℕ (Fin.fromℕ d) (greatest-digit-is-the-Greatest d)))
            ⟩
                ⟦ greatest-digit d ∷ xs ⟧
            □

Maximum? : ∀ {b d o}
    → (xs : Numeral b d o)
    → Dec (Maximum xs)
Maximum? {b} {d} {o} xs with numView b d o
Maximum? xs | NullBase d o = Maximum-NullBase xs
Maximum? xs | NoDigits b o = no (NoDigits-explode xs)
Maximum? xs | AllZeros b   = yes (Maximum-AllZeros xs)
Maximum? xs | Proper b d o proper = no (Maximum-Proper xs proper)
