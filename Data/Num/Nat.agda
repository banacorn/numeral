module Data.Num.Nat where

open import Data.Num.Core renaming
    (   carry to carry'
    ;   carry-lower-bound to carry-lower-bound'
    ;   carry-upper-bound to carry-upper-bound'
    )
open import Data.Num.Maximum
open import Data.Num.Bounded
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

fromNat : ∀ {b d o}
    → {cont : True (Continuous? b (suc d) o)}
    → Nat o
    → Num b (suc d) o
fromNat               (from offset) = z ∙
fromNat {cont = cont} (suc nat)     = 1+ {cont = cont} (fromNat {cont = cont} nat)

toℕ-fromNat : ∀ b d o
    → (cont : True (Continuous? b (suc d) o))
    → (n : ℕ)
    → (p : o ≤ n)
    → ⟦ fromNat {b} {d} {o} {cont = cont} (Nat-fromℕ o n p) ⟧ ≡ n
toℕ-fromNat b d o cont n       p with o ≟ n
toℕ-fromNat b d o cont n       p | yes eq = cong (_+_ zero) eq
toℕ-fromNat b d .0 cont zero z≤n | no ¬eq = refl
toℕ-fromNat b d o cont (suc n) p | no ¬eq =
    begin
        ⟦ 1+ {b} {cont = cont} (fromNat (Nat-fromℕ o n (≤-pred (≤∧≢⇒< p ¬eq)))) ⟧
    ≡⟨ 1+-toℕ {b} (fromNat {cont = cont} (Nat-fromℕ o n (≤-pred (≤∧≢⇒< p ¬eq)))) ⟩
        suc ⟦ fromNat {cont = cont} (Nat-fromℕ o n (≤-pred (≤∧≢⇒< p ¬eq))) ⟧
    -- mysterious agda bug, this refl must stay here
    ≡⟨ refl ⟩
        suc ⟦ fromNat {cont = cont} (Nat-fromℕ o n (≤-pred (≤∧≢⇒< p ¬eq))) ⟧
    ≡⟨ cong suc (toℕ-fromNat b d o cont n (≤-pred (≤∧≢⇒< p ¬eq))) ⟩
        suc n
    ∎
-- -- a partial function that only maps ℕ to Continuous Nums
-- fromℕ : ∀ {b d o}
--     → {cond : N+Closed b d o}
--     → ℕ
--     → Num b (suc d) o
-- fromℕ {cond = cond} zero = z ∙
-- fromℕ {cond = cond} (suc n) = {!   !}

-- fromℕ {cont = cont} zero = z ∙
-- fromℕ {cont = cont} (suc n) = 1+ {cont = cont} (fromℕ {cont = cont} n)

-- toℕ-fromℕ : ∀ {b d o}
--     → {cont : True (Continuous? b (suc d) o)}
--     → (n : ℕ)
--     → ⟦ fromℕ {cont = cont} n ⟧ ≡ n + o
-- toℕ-fromℕ {_} {_} {_} {cont} zero = refl
-- toℕ-fromℕ {b} {d} {o} {cont} (suc n) =
--     begin
--         ⟦ 1+ {cont = cont} (fromℕ {cont = cont} n) ⟧
--     ≡⟨ 1+-toℕ {cont = cont} (fromℕ {cont = cont} n) ⟩
--         suc ⟦ fromℕ {cont = cont} n ⟧
--     ≡⟨ cong suc (toℕ-fromℕ {cont = cont} n) ⟩
--         suc (n + o)
--     ∎
