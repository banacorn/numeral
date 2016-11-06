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
    → (proper : 2 ≤ suc (d + o))
    → (gapped : Gapped#0 b d o)
    → ¬ (Incrementable {suc b} {_} {o} (greatest-digit d ∙))
Continuous-Proper-Gapped-counter-example {b} {d} {o} proper gapped with nextView {b} (greatest-digit d ∙) proper
Continuous-Proper-Gapped-counter-example proper gapped | NeedNoCarry b d o ¬greatest
    = contradiction (greatest-digit-is-the-Greatest d) ¬greatest
Continuous-Proper-Gapped-counter-example proper gapped | IsGapped b d o greatest _
    = IsGapped⇒¬Incrementable (greatest-digit d ∙) greatest proper gapped
Continuous-Proper-Gapped-counter-example proper gapped  | NotGapped b d o greatest ¬gapped
    = contradiction gapped ¬gapped

Continuous-Proper-Gapped#0 : ∀ {b d o}
    → (proper : 2 ≤ suc (d + o))
    → (gapped : Gapped#0 b d o)
    → ¬ (Continuous (suc b) (suc d) o)
Continuous-Proper-Gapped#0 {b} {d} {o} proper gapped cont
    = contradiction (cont counter-example) (Continuous-Proper-Gapped-counter-example proper gapped)
    where
        counter-example : Num (suc b) (suc d) o
        counter-example = greatest-digit d ∙

Continuous-Proper-¬Gapped#0 : ∀ {b d o}
    → (proper : 2 ≤ suc (d + o))
    → (¬gapped : ¬ (Gapped#0 b d o))
    → Continuous (suc b) (suc d) o
Continuous-Proper-¬Gapped#0 proper ¬gapped xs with nextView xs proper
Continuous-Proper-¬Gapped#0 proper ¬gapped xs | NeedNoCarry b d o ¬greatest
    = (next-number-Proper xs proper) , (begin
            ⟦ next-number-Proper xs proper ⟧
        ≡⟨ cong ⟦_⟧ (next-number-Proper-refine xs proper (NeedNoCarry b d o ¬greatest)) ⟩
            ⟦ next-number-Proper-NeedNoCarry xs ¬greatest proper ⟧
        ≡⟨ next-number-Proper-NeedNoCarry-lemma xs ¬greatest proper ⟩
            suc ⟦ xs ⟧
        ∎)
Continuous-Proper-¬Gapped#0 proper ¬gapped (x ∙)    | IsGapped b d o greatest gapped = contradiction gapped ¬gapped
Continuous-Proper-¬Gapped#0 proper ¬gapped (x ∷ xs) | IsGapped b d o greatest gapped
    = contradiction gapped (¬Gapped#0⇒¬Gapped#N xs proper ¬gapped)
Continuous-Proper-¬Gapped#0 proper _ xs | NotGapped b d o greatest ¬gapped
    = (next-number-Proper xs proper) , (begin
        ⟦ next-number-Proper xs proper ⟧
    ≡⟨ cong ⟦_⟧ (next-number-Proper-refine xs proper (NotGapped b d o greatest ¬gapped)) ⟩
        ⟦ next-number-Proper-NotGapped xs greatest proper ¬gapped ⟧
    ≡⟨ next-number-Proper-NotGapped-lemma xs greatest proper ¬gapped ⟩
        suc ⟦ xs ⟧
    ∎)

Continuous-Proper : ∀ b d o
    → (proper : 2 ≤ suc (d + o))
    → Dec (Continuous (suc b) (suc d) o)
Continuous-Proper b d o proper with Gapped#0? b d o
Continuous-Proper b d o proper | yes gapped#0 = no  (Continuous-Proper-Gapped#0 proper gapped#0)
Continuous-Proper b d o proper | no ¬gapped#0 = yes (Continuous-Proper-¬Gapped#0 proper ¬gapped#0)

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
Continuous⇒¬Gapped#0 cont proper gapped#0 = contradiction (toWitness cont) (Continuous-Proper-Gapped#0 proper gapped#0)

-- -- a partial function that only maps ℕ to Continuous Nums
-- fromℕ : ∀ {b d o}
--     → (True (Continuous? b (suc d) o))
--     → (val : ℕ)
--     → (True (o ≤? val))
--     → Num b (suc d) o
-- fromℕ {o = zero} cont zero o≤n = z ∙
-- fromℕ {o = zero} cont (suc n) o≤n = 1+ cont (fromℕ cont n tt)
-- fromℕ {o = suc o} cont zero ()
-- fromℕ {o = suc o} cont (suc n) o≤n with o ≟ n
-- fromℕ {b} {d} {suc o} cont (suc n) o≤n | yes o≡n = z ∙
-- fromℕ {b} {d} {suc o} cont (suc n) o≤n | no  o≢n = 1+ cont (fromℕ cont n (fromWitness o<n))
--     where
--         o<n : o < n
--         o<n = ≤∧≢⇒< (≤-pred (toWitness o≤n)) o≢n
