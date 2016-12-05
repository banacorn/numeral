module Data.Num.Bounded where

open import Data.Num.Digit
open import Data.Num.Core
open import Data.Num.Maximum

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
-- a system is bounded if there exists the greatest number
Bounded : ∀ b d o → Set
Bounded b d o = Σ[ xs ∈ Numeral b d o ] Maximum xs

Bounded-NullBase : ∀ d o → Bounded 0 (suc d) o
Bounded-NullBase d o = (greatest-digit d ∙) , (Maximum-NullBase-Greatest (greatest-digit d ∙) (greatest-digit-is-the-Greatest d))

Bounded-NoDigits : ∀ b o → ¬ (Bounded b 0 o)
Bounded-NoDigits b o (xs , claim) = NoDigits-explode xs

Bounded-AllZeros : ∀ b → Bounded (suc b) 1 0
Bounded-AllZeros b = (z ∙) , Maximum-AllZeros (z ∙)

Bounded-Proper : ∀ b d o → 2 ≤ suc (d + o) → ¬ (Bounded (suc b) (suc d) o)
Bounded-Proper b d o proper (xs , claim) = contradiction p ¬p
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

Bounded? : ∀ b d o → Dec (Bounded b d o)
Bounded? b d o with numView b d o
Bounded? _ _ _ | NullBase d o
    = yes (Bounded-NullBase d o)
Bounded? _ _ _ | NoDigits b o
    = no (Bounded-NoDigits b o)
Bounded? _ _ _ | AllZeros b
    = yes (Bounded-AllZeros b)
Bounded? _ _ _ | Proper b d o proper
    = no (Bounded-Proper b d o proper)


--------------------------------------------------------------------------------
-- Misc

Maximum⇒Bounded : ∀ {b d o}
    → (xs : Numeral b d o)
    → Maximum xs
    → Bounded b d o
Maximum⇒Bounded xs max = xs , max

-- contraposition of Maximum⇒Bounded
¬Bounded⇒¬Maximum : ∀ {b d o}
    → (xs : Numeral b d o)
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
