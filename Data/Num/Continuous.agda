module Data.Num.Continuous where

open import Data.Num.Core
open import Data.Num.Maximum
open import Data.Num.Bounded
open import Data.Num.Next
open import Data.Num.Increment

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

Continuous : ∀ b d o → Set
Continuous b d o = (xs : Numeral b d o) → Incrementable xs

Bounded⇒¬Continuous : ∀ {b d o}
    → Bounded b d o
    → ¬ (Continuous b d o)
Bounded⇒¬Continuous (xs , max) claim = contradiction (claim xs) (Maximum⇒¬Incrementable xs max)

first-endpoint : ∀ b d o → Numeral (suc b) (suc d) o
first-endpoint b d o = greatest-digit d ∙

first-endpoint-¬Incrementable : ∀ {b d o}
    → (proper : 2 ≤ suc (d + o))
    → (gapped : Gapped#0 b d o)
    → ¬ (Incrementable (first-endpoint b d o))
first-endpoint-¬Incrementable {b} {d} {o} proper gapped with nextView (first-endpoint b d o) proper
first-endpoint-¬Incrementable proper gapped | Interval b d o ¬greatest
    = contradiction (greatest-digit-is-the-Greatest d) ¬greatest
first-endpoint-¬Incrementable proper gapped | GappedEndpoint b d o greatest _
    = GappedEndpoint⇒¬Incrementable (first-endpoint b d o) greatest proper gapped
first-endpoint-¬Incrementable proper gapped | UngappedEndpoint b d o greatest ¬gapped
    = contradiction gapped ¬gapped

Gapped#0⇒¬Continuous : ∀ {b d o}
    → (proper : 2 ≤ suc (d + o))
    → (gapped : Gapped#0 b d o)
    → ¬ (Continuous (suc b) (suc d) o)
Gapped#0⇒¬Continuous {b} {d} {o} proper gapped cont
    = contradiction
        (cont (first-endpoint b d o))
        (first-endpoint-¬Incrementable proper gapped)

¬Gapped#0⇒Continuous : ∀ {b d o}
    → (proper : 2 ≤ suc (d + o))
    → (¬gapped : ¬ (Gapped#0 b d o))
    → Continuous (suc b) (suc d) o
¬Gapped#0⇒Continuous proper ¬gapped xs with nextView xs proper
¬Gapped#0⇒Continuous proper ¬gapped xs | Interval b d o ¬greatest
    = (next-numeral-Proper xs proper) , (begin
            ⟦ next-numeral-Proper xs proper ⟧
        ≡⟨ cong ⟦_⟧ (next-numeral-Proper-refine xs proper (Interval b d o ¬greatest)) ⟩
            ⟦ next-numeral-Proper-Interval xs ¬greatest proper ⟧
        ≡⟨ next-numeral-Proper-Interval-lemma xs ¬greatest proper ⟩
            suc ⟦ xs ⟧
        ∎)
¬Gapped#0⇒Continuous proper ¬gapped (x ∙)    | GappedEndpoint b d o greatest gapped
    = contradiction gapped ¬gapped
¬Gapped#0⇒Continuous proper ¬gapped (x ∷ xs) | GappedEndpoint b d o greatest gapped
    = contradiction gapped (¬Gapped#0⇒¬Gapped#N xs proper ¬gapped)
¬Gapped#0⇒Continuous proper _ xs | UngappedEndpoint b d o greatest ¬gapped
    = (next-numeral-Proper xs proper) , (begin
        ⟦ next-numeral-Proper xs proper ⟧
    ≡⟨ cong ⟦_⟧ (next-numeral-Proper-refine xs proper (UngappedEndpoint b d o greatest ¬gapped)) ⟩
        ⟦ next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped ⟧
    ≡⟨ next-numeral-Proper-UngappedEndpoint-lemma xs greatest proper ¬gapped ⟩
        suc ⟦ xs ⟧
    ∎)

Continuous-Proper : ∀ b d o
    → (proper : 2 ≤ suc (d + o))
    → Dec (Continuous (suc b) (suc d) o)
Continuous-Proper b d o proper with Gapped#0? b d o
Continuous-Proper b d o proper | yes gapped#0 = no  (Gapped#0⇒¬Continuous proper gapped#0)
Continuous-Proper b d o proper | no ¬gapped#0 = yes (¬Gapped#0⇒Continuous proper ¬gapped#0)

Continuous? : ∀ b d o → Dec (Continuous b d o)
Continuous? b d o with numView b d o
Continuous? _ _ _ | NullBase d o = no (Bounded⇒¬Continuous (Bounded-NullBase d o))
Continuous? _ _ _ | NoDigits b o = yes (λ xs → NoDigits-explode xs)
Continuous? _ _ _ | AllZeros b = no (Bounded⇒¬Continuous (Bounded-AllZeros b))
Continuous? _ _ _ | Proper b d o proper = Continuous-Proper b d o proper

Continuous⇒¬Gapped#0 : ∀ {b d o}
    → (cont : True (Continuous? (suc b) (suc d) o))
    → (proper : suc d + o ≥ 2)
    → ¬ (Gapped#0 b d o)
Continuous⇒¬Gapped#0 cont proper gapped#0 = contradiction (toWitness cont) (Gapped#0⇒¬Continuous proper gapped#0)

-- -- a partial function that only maps ℕ to Continuous Nums
-- fromℕ : ∀ {b d o}
--     → (True (Continuous? b (suc d) o))
--     → (val : ℕ)
--     → (True (o ≤? val))
--     → Numeral b (suc d) o
-- fromℕ {o = zero} cont zero o≤n = z ∙
-- fromℕ {o = zero} cont (suc n) o≤n = 1+ cont (fromℕ cont n tt)
-- fromℕ {o = suc o} cont zero ()
-- fromℕ {o = suc o} cont (suc n) o≤n with o ≟ n
-- fromℕ {b} {d} {suc o} cont (suc n) o≤n | yes o≡n = z ∙
-- fromℕ {b} {d} {suc o} cont (suc n) o≤n | no  o≢n = 1+ cont (fromℕ cont n (fromWitness o<n))
--     where
--         o<n : o < n
--         o<n = ≤∧≢⇒< (≤-pred (toWitness o≤n)) o≢n
