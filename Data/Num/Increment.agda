module Data.Num.Increment where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next

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
-- a number is incrementable if there exists some n' : Numeral b d o such that ⟦ n' ⟧ℕ ≡ suc ⟦ n ⟧ℕ

Incrementable : ∀ {b d o} → (xs : Numeral b d o) → Set
Incrementable {b} {d} {o} xs = Σ[ xs' ∈ Numeral b d o ] ⟦ xs' ⟧ ≡ suc ⟦ xs ⟧

m≡1+n⇒m>n : ∀ {m n} → m ≡ suc n → m > n
m≡1+n⇒m>n {zero}  {n}  ()
m≡1+n⇒m>n {suc m} {.m} refl = s≤s ≤-refl

Maximum⇒¬Incrementable : ∀ {b d o}
    → (xs : Numeral b d o)
    → (max : Maximum xs)
    → ¬ (Incrementable xs)
Maximum⇒¬Incrementable xs max (evidence , claim)
    = contradiction (max evidence) (>⇒≰ (m≡1+n⇒m>n claim))

GappedEndpoint⇒¬Incrementable : ∀ {b d o}
    → (xs : Numeral (suc b) (suc d) o)
    → (greatest : Greatest (lsd xs))
    → (proper : 2 ≤ suc (d + o))
    → (gapped : Gapped xs proper)
    → ¬ (Incrementable xs)
GappedEndpoint⇒¬Incrementable {b} {d} {o} xs greatest proper gapped (incremented , claim)
    = contradiction ⟦next⟧>⟦incremented⟧ ⟦next⟧≯⟦incremented⟧
    where
        next : Numeral (suc b) (suc d) o
        next = next-numeral-Proper xs proper

        ⟦next⟧>⟦incremented⟧ : ⟦ next ⟧ > ⟦ incremented ⟧
        ⟦next⟧>⟦incremented⟧ =
            start
                suc ⟦ incremented ⟧
            ≈⟨ cong suc claim ⟩
                suc (suc ⟦ xs ⟧)
            ≤⟨ next-numeral-Proper-GappedEndpoint-lemma xs greatest proper gapped ⟩
                ⟦ next-numeral-Proper-GappedEndpoint xs proper gapped ⟧
            ≈⟨ cong ⟦_⟧ (sym (next-numeral-Proper-refine xs proper (GappedEndpoint b d o greatest gapped))) ⟩
                ⟦ next-numeral-Proper xs proper ⟧
            □

        ⟦next⟧≯⟦incremented⟧ : ⟦ next ⟧ ≯ ⟦ incremented ⟧
        ⟦next⟧≯⟦incremented⟧ = ≤⇒≯ $ next-numeral-is-immediate-Proper xs incremented proper (m≡1+n⇒m>n claim)




Incrementable?-Proper : ∀ {b d o}
    → (xs : Numeral (suc b) (suc d) o)
    → (proper : 2 ≤ suc (d + o))
    → Dec (Incrementable xs)
Incrementable?-Proper xs proper with nextView xs proper
Incrementable?-Proper xs proper | Interval b d o ¬greatest
    = yes ((next-numeral-Proper xs proper) , (begin
            ⟦ next-numeral-Proper xs proper ⟧
        ≡⟨ cong ⟦_⟧ (next-numeral-Proper-refine xs proper (Interval b d o ¬greatest)) ⟩
            ⟦ next-numeral-Proper-Interval xs ¬greatest proper ⟧
        ≡⟨ next-numeral-Proper-Interval-lemma xs ¬greatest proper ⟩
            suc ⟦ xs ⟧
        ∎))
Incrementable?-Proper xs proper | GappedEndpoint b d o greatest gapped
    = no (GappedEndpoint⇒¬Incrementable xs greatest proper gapped)
Incrementable?-Proper xs proper | UngappedEndpoint b d o greatest ¬gapped
    = yes ((next-numeral-Proper xs proper) , (begin
            ⟦ next-numeral-Proper xs proper ⟧
        ≡⟨ cong ⟦_⟧ (next-numeral-Proper-refine xs proper (UngappedEndpoint b d o greatest ¬gapped)) ⟩
            ⟦ next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped ⟧
        ≡⟨ next-numeral-Proper-UngappedEndpoint-lemma xs greatest proper ¬gapped ⟩
            suc ⟦ xs ⟧
        ∎))


Incrementable? : ∀ {b d o}
    → (xs : Numeral b d o)
    → Dec (Incrementable xs)
Incrementable? xs with Maximum? xs
Incrementable? xs | yes max = no (Maximum⇒¬Incrementable xs max)
Incrementable? {b} {d} {o} xs | no ¬max with numView b d o
Incrementable? xs | no ¬max | NullBase d o
    = yes ((next-numeral-NullBase xs ¬max) , (next-numeral-NullBase-lemma xs ¬max))
Incrementable? xs | no ¬max | NoDigits b o
    = no (NoDigits-explode xs)
Incrementable? xs | no ¬max | AllZeros b
    = no (contradiction (Maximum-AllZeros xs) ¬max)
Incrementable? xs | no ¬max | Proper b d o proper
    = Incrementable?-Proper xs proper

increment : ∀ {b d o}
    → (xs : Numeral b d o)
    → (incr : True (Incrementable? xs))
    → Numeral b d o
increment xs incr = proj₁ $ toWitness incr

increment-next-numeral-Proper : ∀ {b d o}
    → (xs : Numeral (suc b) (suc d) o)
    → (proper : 2 ≤ suc (d + o))
    → (incr : True (Incrementable?-Proper xs proper))
    → proj₁ (toWitness incr) ≡ next-numeral-Proper xs proper
increment-next-numeral-Proper xs proper incr with nextView xs proper
increment-next-numeral-Proper xs proper incr | Interval b d o ¬greatest = begin
        next-numeral-Proper xs proper
    ≡⟨ next-numeral-Proper-refine xs proper (Interval b d o ¬greatest) ⟩
        next-numeral-Proper-Interval xs ¬greatest proper
    ∎
increment-next-numeral-Proper xs proper ()   | GappedEndpoint b d o greatest gapped
increment-next-numeral-Proper xs proper incr | UngappedEndpoint b d o greatest ¬gapped = begin
        next-numeral-Proper xs proper
    ≡⟨ next-numeral-Proper-refine xs proper (UngappedEndpoint b d o greatest ¬gapped) ⟩
        next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped
    ∎

increment-next-numeral : ∀ {b d o}
    → (xs : Numeral b d o)
    → (¬max : ¬ (Maximum xs))
    → (incr : True (Incrementable? xs))
    → increment xs incr ≡ next-numeral xs ¬max
increment-next-numeral xs ¬max incr with Maximum? xs
increment-next-numeral xs ¬max () | yes max
increment-next-numeral {b} {d} {o} xs ¬max incr | no _  with numView b d o
increment-next-numeral xs _ incr | no ¬max | NullBase d o = refl
increment-next-numeral xs _ ()   | no ¬max | NoDigits b o
increment-next-numeral xs _ ()   | no ¬max | AllZeros b
increment-next-numeral xs _ incr | no ¬max | Proper b d o proper
    = increment-next-numeral-Proper xs proper incr
