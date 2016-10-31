module Data.Num.Continuous where

open import Data.Num.Core
open import Data.Num.Maximum
open import Data.Num.Bounded
open import Data.Num.Next
open import Data.Num.Incrementable

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

Continuous : ∀ b d o → Set
Continuous b d o = (xs : Num b d o) → Incrementable xs

Bounded⇒¬Continuous : ∀ {b d o}
    → Bounded b d o
    → ¬ (Continuous b d o)
Bounded⇒¬Continuous (xs , max) claim = contradiction (claim xs) (Maximum⇒¬Incrementable xs max)

Continuous-Proper-Gapped-counter-example : ∀ {b d o}
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (gapped : Gapped {b} (greatest-digit d ∙) d+o≥2)
    → ¬ (Incrementable {suc b} {_} {o} (greatest-digit d ∙))
Continuous-Proper-Gapped-counter-example {b} {d} {o} d+o≥2 gapped with nextView {b} (greatest-digit d ∙) d+o≥2
Continuous-Proper-Gapped-counter-example d+o≥2 gapped | NeedNoCarry b d o ¬greatest
    = contradiction (greatest-digit-is-the-Greatest d) ¬greatest
Continuous-Proper-Gapped-counter-example d+o≥2 gapped | IsGapped b d o greatest _
    = IsGapped⇒¬Incrementable (greatest-digit d ∙) greatest d+o≥2 gapped
Continuous-Proper-Gapped-counter-example d+o≥2 gapped  | NotGapped b d o greatest ¬gapped
    = contradiction gapped ¬gapped

Continuous-Proper-Gapped : ∀ {b d o}
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (gapped : Gapped {b} (greatest-digit d ∙) d+o≥2)
    → ¬ (Continuous (suc b) (suc d) o)
Continuous-Proper-Gapped {b} {d} {o} d+o≥2 gapped cont
    = contradiction (cont counter-example) (Continuous-Proper-Gapped-counter-example d+o≥2 gapped)
    where
        counter-example : Num (suc b) (suc d) o
        counter-example = greatest-digit d ∙

Continuous-Proper-¬Gapped : ∀ {b d o}
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (¬gapped : suc (suc d) ≰ (1 ⊔ o) * suc b)
    → Continuous (suc b) (suc d) o
Continuous-Proper-¬Gapped d+o≥2 ¬gapped xs with nextView xs d+o≥2
Continuous-Proper-¬Gapped d+o≥2 ¬gapped xs | NeedNoCarry b d o ¬greatest
    = (next-number-Proper xs d+o≥2) , (begin
            ⟦ next-number-Proper xs d+o≥2 ⟧
        ≡⟨ cong ⟦_⟧ (next-number-Proper-refine xs d+o≥2 (NeedNoCarry b d o ¬greatest)) ⟩
            ⟦ next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2 ⟧
        ≡⟨ next-number-Proper-NeedNoCarry-lemma xs ¬greatest d+o≥2 ⟩
            suc ⟦ xs ⟧
        ∎)
Continuous-Proper-¬Gapped d+o≥2 ¬gapped (x ∙)    | IsGapped b d o greatest gapped = contradiction gapped ¬gapped
Continuous-Proper-¬Gapped d+o≥2 ¬gapped (x ∷ xs) | IsGapped b d o greatest gapped
    = contradiction gapped (¬Gapped#0⇒¬Gapped#N xs d+o≥2 ¬gapped)
Continuous-Proper-¬Gapped d+o≥2 _ xs | NotGapped b d o greatest ¬gapped
    = (next-number-Proper xs d+o≥2) , (begin
        ⟦ next-number-Proper xs d+o≥2 ⟧
    ≡⟨ cong ⟦_⟧ (next-number-Proper-refine xs d+o≥2 (NotGapped b d o greatest ¬gapped)) ⟩
        ⟦ next-number-Proper-NotGapped xs greatest d+o≥2 ¬gapped ⟧
    ≡⟨ next-number-Proper-NotGapped-lemma xs greatest d+o≥2 ¬gapped ⟩
        suc ⟦ xs ⟧
    ∎)

Continuous-Proper : ∀ b d o
    → (d+o≥2 : 2 ≤ suc (d + o))
    → Dec (Continuous (suc b) (suc d) o)
Continuous-Proper b d o d+o≥2 with Gapped#0? b d o
Continuous-Proper b d o d+o≥2 | yes gapped#0 = no  (Continuous-Proper-Gapped d+o≥2 gapped#0)
Continuous-Proper b d o d+o≥2 | no ¬gapped#0 = yes (Continuous-Proper-¬Gapped d+o≥2 ¬gapped#0)

Continuous? : ∀ b d o → Dec (Continuous b d o)
Continuous? b d o with numView b d o
Continuous? _ _ _ | NullBase d o = no (Bounded⇒¬Continuous (Bounded-NullBase d o))
Continuous? _ _ _ | NoDigits b o = yes (λ xs → NoDigits-explode xs)
Continuous? _ _ _ | AllZeros b = no (Bounded⇒¬Continuous (Bounded-AllZeros b))
Continuous? _ _ _ | Proper b d o d+o≥2 = Continuous-Proper b d o d+o≥2

1+ : ∀ {b d o}
    → True (Continuous? b d o)
    → (xs : Num b d o)
    → Num b d o
1+ incr xs = proj₁ (toWitness incr xs)

1+-toℕ : ∀ {b d o}
    → (xs : Num b d o)
    → (incr : True (Continuous? b d o))
    → ⟦ 1+ incr xs ⟧ ≡ suc ⟦ xs ⟧
1+-toℕ xs incr = proj₂ (toWitness incr xs)

-- fromℕ : ∀ {b d o}
--     → (incr : True (Continuous? b d o))
--     → ℕ
--     → Num b d o
-- fromℕ incr zero = {!   !}
-- fromℕ incr (suc n) = {!   !}
