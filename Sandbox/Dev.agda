module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
open import Data.Num.Increment
open import Data.Num.Continuous
--
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Nat.DM

open import Data.Fin
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

open import Induction
open import Induction.WellFounded as WF
open import Level using (Lift)

-- _<-Num_ : ∀ {b d o}
--     → (xs ys : Num b d o)
--     → Set
-- xs <-Num ys = ⟦ xs ⟧ < ⟦ ys ⟧

-- Rec : ∀ ℓ b d o → RecStruct (Num b d o) ℓ ℓ
-- Rec ℓ b d o P (x ∙) = Lift ⊤
-- Rec ℓ b d o P (x ∷ xs) = P xs
--
-- rec-builder : ∀ {ℓ b d o} → RecursorBuilder (Rec ℓ b d o)
-- rec-builder P f (x ∙)    = _
-- rec-builder P f (x ∷ xs) = f xs (rec-builder P f xs)
--
-- rec : ∀ {ℓ b d o} → Recursor (Rec ℓ b d o)
-- rec = build rec-builder

-- <-Num-Rec : ∀ {ℓ} b d o → RecStruct (Num b d o) ℓ ℓ
-- <-Num-Rec b d o = WfRec (_<-Num_ {b} {d} {o})
--
-- <-Num-well-founded′ : ∀ b d o xs → <-Num-Rec b d o (Acc _<-Num_) xs
-- <-Num-well-founded′ b d o xs ys p = {!   !}

-- <-well-founded′ : ∀ n → <-Rec (Acc _<′_) n
-- <-well-founded′ zero     _ ()
-- <-well-founded′ (suc n) .n ≤′-refl       = <-well-founded n
-- <-well-founded′ (suc n)  m (≤′-step m<n) = <-well-founded′ n m m<n
--
-- well-founded : ∀ {b d o} → Well-founded (_<-Num_ {b} {d} {o})
-- well-founded (x ∙)    = {!   !}
-- well-founded (x ∷ xs) = {!   !}

-- <-Num-Rec : ∀ {ℓ} → RecStruct

-- <-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
-- <-Rec = WfRec _<′_
