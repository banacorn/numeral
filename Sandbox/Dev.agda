module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
open import Data.Num.Increment
open import Data.Num.Continuous

open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Nat.DM

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


-- Nat-toℕ-fromℕ : ∀ offset
--     → (nat : Nat offset)
--     → (p : offset ≤ (Nat-toℕ nat))
--     → Nat-fromℕ offset (Nat-toℕ nat) p ≡ nat
-- Nat-toℕ-fromℕ offset (from .offset) p with cmp offset (Nat-toℕ (from offset))
-- Nat-toℕ-fromℕ offset (from .offset) p | tri< a ¬b ¬c = contradiction refl ¬b
-- Nat-toℕ-fromℕ zero (from .zero) p | tri≈ ¬a b ¬c = refl
-- Nat-toℕ-fromℕ (suc offset) (from .(suc offset)) p | tri≈ ¬a b ¬c =
--     begin
--         nat-step offset (Nat-fromℕ offset offset (≤-pred p))
--     ≡⟨ cong (nat-step offset) (Nat-toℕ-fromℕ offset (from offset) (≤-pred p)) ⟩
--         from (suc offset)
--     ∎
-- Nat-toℕ-fromℕ offset (from .offset) p | tri> ¬a ¬b c = contradiction refl ¬b
-- Nat-toℕ-fromℕ offset (suc nat) p with cmp offset (Nat-toℕ (suc nat))
-- Nat-toℕ-fromℕ offset (suc nat) p | tri< a ¬b ¬c = cong suc (Nat-toℕ-fromℕ offset nat (≤-pred a))
-- Nat-toℕ-fromℕ zero (suc nat) p | tri≈ ¬a () ¬c
-- Nat-toℕ-fromℕ (suc offset) (suc nat) p | tri≈ ¬a b ¬c with (Nat-fromℕ offset (Nat-toℕ nat) (≤-pred p))
-- Nat-toℕ-fromℕ (suc offset) (suc nat) p | tri≈ ¬a b ¬c | from .offset =
--     begin
--         from (suc offset)
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         suc nat
--     ∎
-- Nat-toℕ-fromℕ (suc offset) (suc nat) p | tri≈ ¬a b ¬c | suc q = {!   !}
