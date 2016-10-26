module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
open import Data.Num.Incrementable
-- open import Data.Num.Continuous

open import Data.Bool
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

Incrementable?-Others : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → (greatest : Greatest (lsd xs))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → Dec (Incrementable xs)
Incrementable?-Others {b} {d} {o} xs ¬max greatest d+o≥2 with othersView xs ¬max d+o≥2 | next-number-Others-¬Incrementable-lemma xs ¬max d+o≥2
Incrementable?-Others xs ¬max greatest d+o≥2 | NeedNoCarry b d o ¬greatest | lemma
    = no (contradiction greatest ¬greatest)
Incrementable?-Others (x ∙) ¬max greatest d+o≥2 | Gapped b d o _ ¬abundant | lemma
    = no (lemma (next-number-suc-Others-Gapped-Single x greatest d+o≥2 (≰⇒> ¬abundant)))
Incrementable?-Others (x ∷ xs) ¬max greatest d+o≥2 | Gapped b d o _ ¬abundant | lemma
    = no (lemma (next-number-suc-Others-Gapped x xs greatest d+o≥2 (≰⇒> ¬abundant)))
Incrementable?-Others (x ∙) ¬max greatest₁ d+o≥2 | ¬Gapped b d o greatest abundant | lemma
    = yes (next , next-number-suc-Others-¬Gapped-Single x greatest d+o≥2 abundant)
    where
        lower-bound : (1 ⊔ o) * suc b > 0
        lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n
        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ LCD d o d+o≥2 ∙
Incrementable?-Others (x ∷ xs) ¬max greatest₁ d+o≥2 | ¬Gapped b d o greatest abundant | lemma
    = yes (next , next-number-suc-Others-¬Gapped x xs greatest d+o≥2 (s≤s abundant))
    where
        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = Maximum-Others xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Others xs ¬max-xs d+o≥2

        gap : ℕ
        gap = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b

        gap-lower-bound : gap > 0
        gap-lower-bound = (start
                1
            ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ xs ⟧))) ⟩
                suc (⟦ xs ⟧ ∸ ⟦ xs ⟧)
            ≈⟨ sym (+-∸-assoc 1 {⟦ xs ⟧} ≤-refl) ⟩
                suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
            ≤⟨ ∸-mono {suc ⟦ xs ⟧} {⟦ next-xs ⟧} {⟦ xs ⟧} (next-number-is-greater-Others xs ¬max-xs d+o≥2) ≤-refl ⟩
                ⟦ next-xs ⟧ ∸ ⟦ xs ⟧
            □) *-mono (s≤s {0} {b} z≤n)

        gap-upper-bound : gap ≤ suc d
        gap-upper-bound = abundant

        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest gap gap-lower-bound ∷ next-xs
