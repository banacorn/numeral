module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
-- open import Data.Num.Incrementable
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

-- next-number-suc-Others-LSD-¬Greatest : ∀ {b d o}
--     → (xs : Num (suc b) (suc d) o)
--     → (¬max : ¬ (Maximum xs))
--     → (¬greatest : ¬ (Greatest (lsd xs)))
--     → (d+o≥2 : 2 ≤ suc (d + o))
--     → ⟦ next-number-Others xs ¬max d+o≥2 ⟧ ≡ suc ⟦ xs ⟧
-- next-number-suc-Others-LSD-¬Greatest {b} {d} {o} (x ∙) ¬max ¬greatest d+o≥2 with Others-view-single b d o x
-- next-number-suc-Others-LSD-¬Greatest {b} {d} {o} (x ∙) ¬max ¬greatest d+o≥2 | NeedNoCarry _
--     = next-number-Others-NeedNoCarry-Single {b} {d} {o} x ¬greatest
-- next-number-suc-Others-LSD-¬Greatest {b} {d} {o} (x ∙) ¬max ¬greatest d+o≥2 | Gapped greatest gapped
--     = contradiction greatest ¬greatest
-- next-number-suc-Others-LSD-¬Greatest {b} {d} {o} (x ∙) ¬max ¬greatest d+o≥2 | ¬Gapped greatest ¬gapped
--     = contradiction greatest ¬greatest
-- next-number-suc-Others-LSD-¬Greatest {b} {d} {o} (x ∷ xs) ¬max ¬greatest d+o≥2 with Others-view x xs ¬max d+o≥2
-- next-number-suc-Others-LSD-¬Greatest {b} {d} {o} (x ∷ xs) ¬max ¬greatest d+o≥2 | NeedNoCarry _
--     = next-number-Others-NeedNoCarry x xs ¬greatest
-- next-number-suc-Others-LSD-¬Greatest {b} {d} {o} (x ∷ xs) ¬max ¬greatest d+o≥2 | Gapped greatest gapped
--     = contradiction greatest ¬greatest
-- next-number-suc-Others-LSD-¬Greatest {b} {d} {o} (x ∷ xs) ¬max ¬greatest d+o≥2 | ¬Gapped greatest ¬gapped
--     = contradiction greatest ¬greatest
--
