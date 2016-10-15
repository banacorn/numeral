module Data.Num.Maximum where

open import Data.Num.Core
open import Data.Num.Bounded

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

Maximum-unique : ∀ {b d o}
    → (max xs : Num b d o)
    → Maximum max
    → Maximum xs
    → ⟦ max ⟧ ≡ ⟦ xs ⟧
Maximum-unique max xs max-max xs-max = IsPartialOrder.antisym isPartialOrder
    (xs-max max)
    (max-max xs)

Maximum? : ∀ {b d o}
    → (xs : Num b d o)
    → Dec (Maximum xs)
Maximum? {b} {d} {o} xs with boundedView b d o
Maximum? xs | IsBounded cond with BoundedCond⇒Bounded cond
Maximum? xs | IsBounded cond | max , claim with ⟦ max ⟧ ≟ ⟦ xs ⟧
Maximum? xs | IsBounded cond | max , claim | yes p rewrite p = yes claim
Maximum? xs | IsBounded cond | max , claim | no ¬p = no (contraposition (Maximum-unique max xs claim) ¬p)
Maximum? xs | IsntBounded cond = no (¬Bounded⇒¬Maximum xs (NonBoundedCond⇒¬Bounded cond))
