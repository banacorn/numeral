module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
open import Data.Num.Increment
open import Data.Num.Continuous

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


-- left-bounded infinite interval of natural number
data Nat : ℕ → Set where
    from : ∀ offset   → Nat offset
    suc  : ∀ {offset} → Nat offset → Nat offset

Nat-toℕ : ∀ {offset} → Nat offset → ℕ
Nat-toℕ (from offset) = offset
Nat-toℕ (suc n)       = suc (Nat-toℕ n)

Nat-fromℕ : ∀ offset
    → (n : ℕ)
    → .(offset ≤ n)
    → Nat offset
Nat-fromℕ offset n       p with offset ≟ n
Nat-fromℕ offset n       p | yes eq = from offset
Nat-fromℕ offset zero    p | no ¬eq = from offset
Nat-fromℕ offset (suc n) p | no ¬eq = suc (Nat-fromℕ offset n (≤-pred (≤∧≢⇒< p ¬eq)))


Nat-fromℕ-toℕ : ∀ offset
    → (n : ℕ)
    → (p : offset ≤ n)
    → Nat-toℕ (Nat-fromℕ offset n p) ≡ n
Nat-fromℕ-toℕ offset n       p with offset ≟ n
Nat-fromℕ-toℕ offset n       p | yes eq = eq
Nat-fromℕ-toℕ .0      zero z≤n | no ¬eq = refl
Nat-fromℕ-toℕ offset (suc n) p | no ¬eq =
    begin
        suc (Nat-toℕ (Nat-fromℕ offset n (≤-pred (≤∧≢⇒< p ¬eq))))
    ≡⟨ cong suc (Nat-fromℕ-toℕ offset n (≤-pred (≤∧≢⇒< p ¬eq))) ⟩
        suc n
    ∎


-- cong suc (Nat-toℕ-fromℕ offset nat (≤-pred (≤∧≢⇒< p ¬eq)))
-- Nat-toℕ-fromℕ : ∀ offset
--     → (nat : Nat offset)
--     → (p : offset ≤ (Nat-toℕ nat))
--     → Nat-fromℕ offset (Nat-toℕ nat) p ≡ nat
-- Nat-toℕ-fromℕ offset nat p with cmp offset (Nat-toℕ nat)
-- Nat-toℕ-fromℕ offset nat p | tri< a ¬b ¬c = {!   !}
-- Nat-toℕ-fromℕ offset nat p | tri≈ ¬a b ¬c = {!   !}
-- Nat-toℕ-fromℕ offset nat p | tri> ¬a ¬b c = {!   !}



-- data Nat : ℕ → Set where
--     from : ∀ {offset} → ∀ n → .(n ≡ offset) → Nat offset
--     suc  : ∀ {offset} → Nat offset → Nat offset
--
-- Nat-toℕ : ∀ {offset} → Nat offset → ℕ
-- Nat-toℕ (from n eq)   = n
-- Nat-toℕ (suc n)       = suc (Nat-toℕ n)
--
-- -- nat-step : ∀ offset
-- --     → Nat offset
-- --     → Nat (suc offset)
-- -- nat-step offset (from .offset) = from (suc offset)
-- -- nat-step offset (suc nat)      = suc (nat-step offset nat)
-- --
-- -- nat-step-toℕ : ∀ offset
-- --     → (nat : Nat offset)
-- --     → Nat-toℕ (nat-step offset nat) ≡ suc (Nat-toℕ nat)
-- -- nat-step-toℕ offset (from .offset) = {!   !}
-- -- nat-step-toℕ offset (suc nat) = cong suc (nat-step-toℕ offset nat)
--
-- Nat-fromℕ : ∀ offset
--     → (n : ℕ)
--     → offset ≤ n
--     → Nat offset
-- Nat-fromℕ offset n       p with cmp offset n
-- Nat-fromℕ .0 zero z≤n | tri< a ¬b ¬c = from zero refl
-- Nat-fromℕ offset (suc n) p | tri< a ¬b ¬c = suc (Nat-fromℕ offset n (≤-pred a))
-- Nat-fromℕ offset n       p | tri≈ ¬a b ¬c = from n (sym b)
-- -- Nat-fromℕ offset n       p | tri≈ ¬a refl ¬c = from (suc n)
-- Nat-fromℕ offset n       p | tri> ¬a ¬b c = contradiction p (<⇒≱ c)
--
-- -- Nat-fromℕ-toℕ : ∀ offset
-- --     → (n : ℕ)
-- --     → (p : offset ≤ n)
-- --     → Nat-toℕ (Nat-fromℕ offset n p) ≡ n
-- -- Nat-fromℕ-toℕ offset n       p with cmp offset n
-- -- Nat-fromℕ-toℕ .0     zero  z≤n | tri< a ¬b ¬c = refl
-- -- Nat-fromℕ-toℕ offset (suc n) p | tri< a ¬b ¬c = cong suc (Nat-fromℕ-toℕ offset n (≤-pred a))
-- -- Nat-fromℕ-toℕ .0 zero p | tri≈ ¬a refl ¬c = refl
-- -- Nat-fromℕ-toℕ offset (suc n) p | tri≈ ¬a b ¬c = b
-- -- Nat-fromℕ-toℕ offset n       p | tri> ¬a ¬b c = contradiction p (<⇒≱ c)
--
-- Nat-toℕ-fromℕ : ∀ offset
--     → (nat : Nat offset)
--     → (p : offset ≤ (Nat-toℕ nat))
--     → Nat-fromℕ offset (Nat-toℕ nat) p ≡ nat
-- Nat-toℕ-fromℕ offset nat p with cmp offset (Nat-toℕ nat)
-- Nat-toℕ-fromℕ offset (from n x) p | tri< a ¬b ¬c = {!   !}
-- Nat-toℕ-fromℕ offset (suc nat) p | tri< a ¬b ¬c = cong suc (Nat-toℕ-fromℕ offset nat (≤-pred a))
-- Nat-toℕ-fromℕ offset (from zero x) p | tri≈ ¬a b ¬c = refl
-- Nat-toℕ-fromℕ offset (from (suc n) x) p | tri≈ ¬a b ¬c = refl
-- Nat-toℕ-fromℕ offset (suc nat) p | tri≈ ¬a b ¬c = {!   !}
-- Nat-toℕ-fromℕ offset nat p | tri> ¬a ¬b c = {! contradiction p (<⇒≱ ?)  !}
-- -- Nat-toℕ-fromℕ : ∀ offset
-- --     → (nat : Nat offset)
-- --     → (p : offset ≤ (Nat-toℕ nat))
-- --     → Nat-fromℕ offset (Nat-toℕ nat) p ≡ nat
-- -- Nat-toℕ-fromℕ offset nat p with (Nat-toℕ nat) | cmp offset (Nat-toℕ nat)
-- -- Nat-toℕ-fromℕ offset nat p | q | tri< a ¬b ¬c = {!   !}
-- -- Nat-toℕ-fromℕ .0 (from .0) p | zero | tri≈ ¬a refl ¬c = refl
-- -- Nat-toℕ-fromℕ .0 (suc nat) z≤n | zero | tri≈ ¬a refl ¬c = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p | suc q | tri≈ ¬a b ¬c = {! q  !}
-- -- Nat-toℕ-fromℕ offset nat p | q | tri> ¬a ¬b c = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p with cmp offset (Nat-toℕ nat)
-- -- Nat-toℕ-fromℕ offset (from .offset) p | tri< a ¬b ¬c = contradiction refl ¬b
-- -- Nat-toℕ-fromℕ offset (suc nat) p | tri< a ¬b ¬c = cong suc (Nat-toℕ-fromℕ offset nat (≤-pred a))
-- -- Nat-toℕ-fromℕ offset (from .offset) p | tri≈ ¬a b ¬c with (Nat-toℕ (from offset))
-- -- Nat-toℕ-fromℕ offset (from .offset) p | tri≈ ¬a b ¬c | zero = {!   !}
-- -- Nat-toℕ-fromℕ offset (from .offset) p | tri≈ ¬a b ¬c | suc q = {!   !}
-- -- Nat-toℕ-fromℕ offset (suc nat) p | tri≈ ¬a b ¬c = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p | tri> ¬a ¬b c = {!   !}
--
--
-- -- Nat-toℕ-fromℕ offset nat p with (Nat-toℕ nat) | cmp offset (Nat-toℕ nat)
-- -- Nat-toℕ-fromℕ offset (from .offset) p | zero | tri< a ¬b ¬c = refl
-- -- Nat-toℕ-fromℕ offset (suc nat) p | zero | tri< () ¬b ¬c
-- -- Nat-toℕ-fromℕ offset (from .offset) p | suc q | tri< a ¬b ¬c = {!   !}
-- -- Nat-toℕ-fromℕ offset (suc nat) p | suc q | tri< a ¬b ¬c = cong suc {!  Nat-toℕ-fromℕ offset  !}
-- -- Nat-toℕ-fromℕ offset nat p | q | tri≈ ¬a b ¬c = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p | q | tri> ¬a ¬b c = {!   !}
--
-- -- Nat-toℕ-fromℕ offset (from .offset) p | zero | tri< a ¬b ¬c = refl
-- -- Nat-toℕ-fromℕ offset (suc nat) p | zero | tri< a ¬b ¬c = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p | zero | tri≈ ¬a b ¬c = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p | zero | tri> ¬a ¬b c = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p | suc q | r = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p with (Nat-toℕ nat) | cmp offset (Nat-toℕ nat)
-- -- Nat-toℕ-fromℕ offset nat p | zero | tri< a ¬b ¬c = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p | zero | tri≈ ¬a b ¬c = {!   !}
-- -- Nat-toℕ-fromℕ offset nat p | zero | tri> ¬a ¬b c = contradiction p (<⇒≱ c)
-- -- Nat-toℕ-fromℕ offset nat p | suc q | r = {!   !}
--
-- -- Nat-toℕ-fromℕ : ∀ offset
-- --     → (nat : Nat offset)
-- --     → (p : offset ≤ (Nat-toℕ nat))
-- --     → Nat-fromℕ offset (Nat-toℕ nat) p ≡ nat
-- -- Nat-toℕ-fromℕ offset (from .offset) p with cmp offset (Nat-toℕ (from offset))
-- -- Nat-toℕ-fromℕ offset (from .offset) p | tri< a ¬b ¬c = contradiction refl ¬b
-- -- Nat-toℕ-fromℕ zero (from .zero) p | tri≈ ¬a b ¬c = refl
-- -- Nat-toℕ-fromℕ (suc offset) (from .(suc offset)) p | tri≈ ¬a b ¬c =
-- --     begin
-- --         nat-step offset (Nat-fromℕ offset offset (≤-pred p))
-- --     ≡⟨ cong (nat-step offset) (Nat-toℕ-fromℕ offset (from offset) (≤-pred p)) ⟩
-- --         from (suc offset)
-- --     ∎
-- -- Nat-toℕ-fromℕ offset (from .offset) p | tri> ¬a ¬b c = contradiction refl ¬b
-- -- Nat-toℕ-fromℕ offset (suc nat) p with cmp offset (Nat-toℕ (suc nat))
-- -- Nat-toℕ-fromℕ offset (suc nat) p | tri< a ¬b ¬c = cong suc (Nat-toℕ-fromℕ offset nat (≤-pred a))
-- -- Nat-toℕ-fromℕ zero (suc nat) p | tri≈ ¬a () ¬c
-- -- Nat-toℕ-fromℕ (suc offset) (suc nat) p | tri≈ ¬a b ¬c with (Nat-fromℕ offset (Nat-toℕ nat) (≤-pred p))
-- -- Nat-toℕ-fromℕ (suc offset) (suc nat) p | tri≈ ¬a b ¬c | from .offset =
-- --     begin
-- --         from (suc offset)
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         suc nat
-- --     ∎
-- -- Nat-toℕ-fromℕ (suc offset) (suc nat) p | tri≈ ¬a b ¬c | suc q = {!   !}
