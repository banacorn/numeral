module Sandbox.Dev where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next
open import Data.Num.Incrementable
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

sum : ∀ {d}
    → (o : ℕ)
    → (x y : Digit (suc d))
    → ℕ
sum o x y = Digit-toℕ x o + Digit-toℕ y o

sum≥o : ∀ {d} o
    → (x y : Digit (suc d))
    → sum o x y ≥ o
sum≥o o x y = start
        o
    ≤⟨ m≤n+m o (Fin.toℕ x) ⟩
        Digit-toℕ x o
    ≤⟨ m≤m+n (Digit-toℕ x o) (Digit-toℕ y o) ⟩
        sum o x y
    □

sum-upper-bound : ∀ {d} o
    → (x y : Digit (suc d))
    → sum o x y ≤ (d + o) + (d + o)
sum-upper-bound {d} o x y =
    start
        Digit-toℕ x o + Digit-toℕ y o
    ≤⟨ ≤-pred (Digit<d+o x o) +-mono ≤-pred (Digit<d+o y o) ⟩
        d + o + (d + o)
    □

--  0   o                d+o          d+o+(1⊔o)×b
----|---|-----------------|----------------|
--    o          d              (1⊔o)×b
--                        [----------------] "buffer capacity"


data Sum : (b d o : ℕ) (x y : Digit (suc d)) → Set where
    Below : ∀ {b d o x y}
        → (leftover : Digit (suc d))
        → (property : Digit-toℕ leftover o ≡ sum o x y)
        → Sum b d o x y
    Within : ∀ {b d o x y}
        → (leftover : Digit (suc d))
        → (property : Digit-toℕ leftover o + (1 ⊔ o) * suc (suc b) ≡ sum o x y)
        → Sum b d o x y
    Above : ∀ {b d o x y}
        → (leftover carry : Digit (suc d))
        → (property : Digit-toℕ leftover o + (Digit-toℕ carry o) * suc (suc b) ≡ sum o x y)
        → Sum b d o x y



sumView : ∀ b d o
    → (¬gapped : (1 ⊔ o) * suc (suc b) ≤ suc d)
    → (proper : suc d + o ≥ 2)
    → (x y : Digit (suc d))
    → Sum b d o x y
sumView b d o ¬gapped proper x y with (sum o x y) ≤? d + o
sumView b d o ¬gapped proper x y | yes below
    = Below
        (Digit-fromℕ leftover o leftover-upper-bound)
        property
    where
        leftover : ℕ
        leftover = sum o x y

        leftover-upper-bound : leftover ≤ d + o
        leftover-upper-bound = below

        property :
              Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
            ≡ sum o x y
        property =
            begin
                Digit-toℕ (Digit-fromℕ (sum o x y) o below) o
            ≡⟨ Digit-toℕ-fromℕ (sum o x y) (sum≥o o x y) below ⟩
                sum o x y
            ∎
sumView b d o ¬gapped proper x y | no ¬below with (sum o x y) ≤? d + o + (1 ⊔ o) * (suc (suc b))
sumView b d o ¬gapped proper x y | no ¬below | yes within
    = Within
        (Digit-fromℕ leftover o leftover-upper-bound)
        property

    where
        base : ℕ
        base = suc (suc b)

        carry : ℕ
        carry = 1 ⊔ o

        sum≥carry*base : sum o x y ≥ carry * base
        sum≥carry*base =
            start
                (1 ⊔ o) * base
            ≤⟨ m≤m+n ((1 ⊔ o) * base) o ⟩
                (1 ⊔ o) * base + o
            ≤⟨ +n-mono o ¬gapped ⟩
                suc (d + o)
            ≤⟨ ≰⇒> ¬below ⟩
                sum o x y
            □


        leftover : ℕ
        leftover = sum o x y ∸ carry * base

        leftover-lower-bound : leftover ≥ o
        leftover-lower-bound =
            start
                o
            ≈⟨ sym (m+n∸n≡m o (carry * base)) ⟩
                o + carry * base ∸ carry * base
            ≈⟨ cong (λ w → w ∸ carry * base) (+-comm o (carry * base)) ⟩
                carry * base + o ∸ carry * base
            ≤⟨ ∸n-mono (carry * base) (+n-mono o ¬gapped) ⟩
                suc d + o ∸ carry * base
            ≤⟨ ∸n-mono (carry * base) (≰⇒> ¬below) ⟩
                leftover
            □


        leftover-upper-bound : leftover ≤ d + o
        leftover-upper-bound = +n-mono-inverse (carry * base) $
            start
                leftover + carry * base
            ≈⟨ refl ⟩
                sum o x y ∸ carry * base + carry * base
            ≈⟨ m∸n+n≡m sum≥carry*base ⟩
                sum o x y
            ≤⟨ within ⟩
                d + o + carry * base
            □

        property :
              Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
            + carry * base
            ≡ sum o x y
        property =
            begin
                Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o + carry * base
            ≡⟨ cong
                (λ w → w + carry * base)
                (Digit-toℕ-fromℕ leftover leftover-lower-bound leftover-upper-bound)
            ⟩
                (sum o x y ∸ carry * base) + carry * base
            ≡⟨ m∸n+n≡m sum≥carry*base ⟩
                sum o x y
            ∎
sumView b d o ¬gapped proper x y | no ¬below | no ¬within with (sum o x y ∸ ((d + o) + (1 ⊔ o) * (suc (suc b)))) divMod (suc (suc b))
sumView b d o ¬gapped proper x y | no ¬below | no ¬within | result quotient remainder divModProp _ _
    = Above
        (Digit-fromℕ leftover o leftover-upper-bound)
        (Digit-fromℕ carry    o carry-upper-bound)
        property
    where

        base : ℕ
        base = suc (suc b)

        -- divModProp' : sum o x y ≡ Fin.toℕ remainder + ((1 ⊔ o) + quotient) * base + (d + o)
        -- divModProp' =
        --     begin
        --         sum o x y
        --     ≡⟨ sym (m∸n+n≡m (<⇒≤ (≰⇒> ¬within))) ⟩
        --         (sum o x y ∸ ((d + o) + (1 ⊔ o) * base)) + ((d + o) + (1 ⊔ o) * base)
        --     ≡⟨ cong (λ w → w + ((d + o) + (1 ⊔ o) * base)) divModProp ⟩
        --         Fin.toℕ remainder + quotient * base + ((d + o) + (1 ⊔ o) * base)
        --     ≡⟨ cong (λ w → Fin.toℕ remainder + quotient * base + w) (+-comm (d + o) ((1 ⊔ o) * base)) ⟩
        --         Fin.toℕ remainder + quotient * base + ((1 ⊔ o) * base + (d + o))
        --     ≡⟨ +-assoc (Fin.toℕ remainder) (quotient * base) ((1 ⊔ o) * base + (d + o)) ⟩
        --         Fin.toℕ remainder + (quotient * base + ((1 ⊔ o) * base + (d + o)))
        --     ≡⟨ cong (λ w → Fin.toℕ remainder + w) (sym (+-assoc (quotient * base) ((1 ⊔ o) * base) {!   !})) ⟩
        --         {!   !}
        --     ≡⟨ {!   !} ⟩
        --         {!   !}
        --     ≡⟨ {!   !} ⟩
        --         {!   !}
        --     ≡⟨ {!   !} ⟩
        --         Fin.toℕ remainder + ((1 ⊔ o) + quotient) * base + (d + o)
        --     ∎


        carry : ℕ
        carry = (1 ⊓ Fin.toℕ remainder) + (1 ⊔ o) + quotient

        divModProp' : sum o x y ≡ Fin.toℕ remainder + quotient * base + (d + o + (1 ⊔ o) * base)
        divModProp' =
            begin
                sum o x y
            ≡⟨ sym (m∸n+n≡m (<⇒≤ (≰⇒> ¬within))) ⟩
                sum o x y ∸ (d + o + (1 ⊔ o) * base) + (d + o + (1 ⊔ o) * base)
            ≡⟨ cong (λ w → w + ((d + o) + (1 ⊔ o) * base)) divModProp ⟩
                Fin.toℕ remainder + quotient * base + ((d + o) + (1 ⊔ o) * base)
            ∎

        lemma :
              (remainder : Fin base)
            → (prop : sum o x y ∸ (d + o + (1 ⊔ o) * base) ≡ Fin.toℕ remainder + quotient * base)
            → sum o x y ≤ d + o + ((1 ⊓ Fin.toℕ remainder) + (1 ⊔ o) + quotient) * base
        lemma z prop =
            start
                sum o x y
            ≈⟨ sym (m∸n+n≡m (<⇒≤ (≰⇒> ¬within))) ⟩
                (sum o x y ∸ ((d + o) + (1 ⊔ o) * base)) + ((d + o) + (1 ⊔ o) * base)
            ≈⟨ cong (λ w → w + ((d + o) + (1 ⊔ o) * base)) prop ⟩
                quotient * base + ((d + o) + (1 ⊔ o) * base)
            ≈⟨ a+[b+c]≡b+[a+c] (quotient * base) (d + o) ((1 ⊔ o) * base) ⟩
                d + o + (quotient * base + (1 ⊔ o) * base)
            ≈⟨ cong (λ w → d + o + w) (sym (distribʳ-*-+ base quotient (1 ⊔ o))) ⟩
                d + o + (quotient + (1 ⊔ o)) * base
            ≈⟨ cong (λ w → d + o + w * base) (+-comm quotient (1 ⊔ o)) ⟩
                d + o + (1 ⊔ o + quotient) * base
            □
        lemma (s r) prop =
            start
                sum o x y
            ≈⟨ sym (m∸n+n≡m (<⇒≤ (≰⇒> ¬within))) ⟩
                (sum o x y ∸ ((d + o) + (1 ⊔ o) * base)) + ((d + o) + (1 ⊔ o) * base)
            ≈⟨ cong (λ w → w + ((d + o) + (1 ⊔ o) * base)) prop ⟩
                suc (Fin.toℕ r) + quotient * base + ((d + o) + (1 ⊔ o) * base)
            ≈⟨ a+[b+c]≡b+[a+c] (suc (Fin.toℕ r) + quotient * base) (d + o) ((1 ⊔ o) * base) ⟩
                d + o + (suc (Fin.toℕ r) + quotient * base + (1 ⊔ o) * base)
            ≤⟨ n+-mono (d + o)
                (+n-mono ((1 ⊔ o) * base)
                    (+n-mono (quotient * base)
                        (≤-step (bounded r)))) ⟩
                d + o + (suc quotient * base + (1 ⊔ o) * base)
            ≈⟨ cong (λ w → d + o + w) (sym (distribʳ-*-+ base (suc quotient) (1 ⊔ o))) ⟩
                d + o + (1 + (quotient + (1 ⊔ o))) * base
            ≈⟨ cong (λ w → d + o + (1 + w) * base) (+-comm quotient (1 ⊔ o)) ⟩
                d + o + ((1 + (1 ⊔ o + quotient)) * base)
            ≈⟨ refl ⟩
                d + o + ((1 ⊓ (Fin.toℕ (s r))) + (1 ⊔ o) + quotient) * base
            □
        -- dividend
        dividend : ℕ
        dividend = sum o x y ∸ ((d + o) + (1 ⊔ o) * base)

        -- carry : ℕ
        -- carry = (1 ⊓ Fin.toℕ remainder) + quotient

        leftover : ℕ
        leftover = sum o x y ∸ carry * base

        leftover-upper-bound : leftover ≤ d + o
        leftover-upper-bound =
            start
                leftover
            ≈⟨ refl ⟩
                sum o x y ∸ carry * base
            ≈⟨ cong (λ w → w ∸ carry * base) divModProp' ⟩
                Fin.toℕ remainder + quotient * base + (d + o + (1 ⊔ o) * base) ∸ carry * base
            ≈⟨ cong (λ w → w ∸ carry * base) (a+[b+c]≡b+[a+c] (Fin.toℕ remainder + quotient * base) (d + o) ((1 ⊔ o) * base)) ⟩
                d + o + (Fin.toℕ remainder + quotient * base + (1 ⊔ o) * base) ∸ carry * base
            ≈⟨ {!   !} ⟩
                {!   !}
            ≈⟨ {!   !} ⟩
                {!   !}
            ≈⟨ {!   !} ⟩
                {!   !}
            ≈⟨ {!   !} ⟩
                d + o
            □
            -- start
            --     leftover
            -- ≈⟨ refl ⟩
            --     sum o x y ∸ carry * base
            -- ≈⟨ cong (λ w → w ∸ carry * base) divModProp' ⟩
            --     Fin.toℕ remainder + quotient * base + (d + o + (1 ⊔ o) * base) ∸ carry * base
            -- ≤⟨ n∸-mono (Fin.toℕ remainder + quotient * base + (d + o + (1 ⊔ o) * base)) (
            --     start
            --         Fin.toℕ remainder + quotient * base + ((1 ⊔ o) * base)
            --     ≤⟨ {!   !} ⟩
            --         {!   !}
            --     ≤⟨ {!   !} ⟩
            --         {!   !}
            --     ≤⟨ {!   !} ⟩
            --         {!   !}
            --     ≤⟨ {!   !} ⟩
            --         {!  !}
            --     ≈⟨ {!   !} ⟩
            --         {!   !}
            --     ≈⟨ {!   !} ⟩
            --         {!   !}
            --     ≈⟨ {!   !} ⟩
            --         ((1 ⊓ Fin.toℕ remainder) + quotient) * base
            --     ≈⟨ refl ⟩
            --         carry * base
            --     □
            -- ) ⟩
            --     Fin.toℕ remainder + quotient * base + (d + o + ((1 ⊔ o) * base)) ∸ ((Fin.toℕ remainder + quotient * base) + ((1 ⊔ o) * base))
            -- ≈⟨ sym (∸-+-assoc (Fin.toℕ remainder + quotient * base + (d + o + ((1 ⊔ o) * base))) (Fin.toℕ remainder + quotient * base) ((1 ⊔ o) * base)) ⟩
            --     Fin.toℕ remainder + quotient * base + (d + o + ((1 ⊔ o) * base)) ∸ (Fin.toℕ remainder + quotient * base) ∸ ((1 ⊔ o) * base)
            -- ≈⟨ cong (λ w → w ∸ (Fin.toℕ remainder + quotient * base) ∸ ((1 ⊔ o) * base)) (+-comm (Fin.toℕ remainder + quotient * base) (d + o + ((1 ⊔ o) * base))) ⟩
            --     (d + o + ((1 ⊔ o) * base)) + (Fin.toℕ remainder + quotient * base) ∸ (Fin.toℕ remainder + quotient * base) ∸ ((1 ⊔ o) * base)
            -- ≈⟨ cong (λ w → w ∸ ((1 ⊔ o) * base)) (m+n∸n≡m (d + o + ((1 ⊔ o) * base)) (Fin.toℕ remainder + quotient * base)) ⟩
            --     d + o + ((1 ⊔ o) * base) ∸ ((1 ⊔ o) * base)
            -- ≈⟨ m+n∸n≡m (d + o) (((1 ⊔ o) * base)) ⟩
            --     d + o
            -- □


        carry-upper-bound : carry ≤ d + o
        carry-upper-bound = {!   !}


        property = {!   !}

-- sumView : ∀ b d o
--     → (¬gapped : (1 ⊔ o) * suc (suc b) ≤ suc d)
--     → (proper : suc d + o ≥ 2)
--     → (y : Digit (suc d))
--     → (xs : Num (suc (suc b)) (suc d) o)
--     → Sum b d o y (lsd xs)
-- sumView b d o ¬gapped proper y xs with (sum o y (lsd xs)) ≤? d + o
-- sumView b d o ¬gapped proper y xs | yes p
--     = NeedNoCarry
--         (Digit-fromℕ (sum o y (lsd xs)) o leftover-upper-bound)
--         property
--     where
--         leftover : ℕ
--         leftover = sum o y (lsd xs)
--
--         leftover-upper-bound : leftover ≤ d + o
--         leftover-upper-bound = p
--
--         property :
--               Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
--             ≡ sum o y (lsd xs)
--         property =
--             begin
--                 Digit-toℕ (Digit-fromℕ (sum o y (lsd xs)) o p) o
--             ≡⟨ Digit-toℕ-fromℕ (sum o y (lsd xs)) (sum≥o o y (lsd xs)) p ⟩
--                 sum o y (lsd xs)
--             ∎
-- sumView b d o ¬gapped proper y xs | no ¬p with _divMod_ (sum o y (lsd xs) ∸ (d + o + (1 ⊔ o) * (suc (suc b)))) (suc (suc b))
-- sumView b d o ¬gapped proper y xs | no ¬p | result quotient remainder divModProp _ _
--     = Carried
--         (Digit-fromℕ leftover o leftover-upper-bound)
--         (Digit-fromℕ carry o carry-upper-bound)
--         property
--     where
--
--         base : ℕ
--         base = suc (suc b)
--
--         -- dividend
--         dividend : ℕ
--         dividend = sum o y (lsd xs) ∸ (d + o + (1 ⊔ o) * base)
--
--         -- dividend-upper-bound : dividend ≤ d + o
--         -- dividend-upper-bound =
--         --     start
--         --         sum o y (lsd xs) ∸ (d + o + (1 ⊔ o) * base)
--         --     -- ≈⟨ divModProp ⟩
--         --     --     Fin.toℕ remainder + quotient * suc (suc b)
--         --     ≤⟨ n∸-mono (sum o y (lsd xs)) (n+-mono (d + o) {! ¬gapped  !}) ⟩
--         --         {!   !}
--         --     ≤⟨ {!   !} ⟩
--         --         {!   !}
--         --     ≤⟨ {!   !} ⟩
--         --         {!   !}
--         --     ≤⟨ {!   !} ⟩
--         --         d + o
--         --     □
--             -- +n-mono-inverse (d + o) $
--             -- start
--             --     {!  !}
--             -- ≤⟨ {!   !} ⟩
--             --     {!   !}
--             -- ≤⟨ {!   !} ⟩
--             --     {!   !}
--             -- ≤⟨ {!   !} ⟩
--             --     {!   !}
--             -- ≤⟨ {!   !} ⟩
--             --     {!   !}
--             -- □
--             -- start
--             --     sum o y (lsd xs) ∸ (d + o) + (1 ⊔ o) * base + (d + o)
--             -- ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
--             --     sum o y (lsd xs)
--             -- ≤⟨ sum-upper-bound o y (lsd xs) ⟩
--             --     d + o + (d + o)
--             -- □
--
--         divModProp' : sum o y (lsd xs) ≡ Fin.toℕ remainder + quotient * base + (d + o)
--         divModProp' = {!   !}
--         -- divModProp' = cancel-∸-right (d + o) (<⇒≤ (≰⇒> ¬p)) (m≤n+m (d + o) (Fin.toℕ remainder + quotient * base)) $
--             -- begin
--             --     sum o y (lsd xs) ∸ (d + o)
--             -- ≡⟨ refl ⟩
--             --     dividend
--             -- ≡⟨ divModProp ⟩
--             --     Fin.toℕ remainder + quotient * base
--             -- ≡⟨ sym (m+n∸n≡m (Fin.toℕ remainder + quotient * base) (d + o)) ⟩
--             --     Fin.toℕ remainder + quotient * base + (d + o) ∸ (d + o)
--             -- ∎
--
--
--         -- carry
--         carry : ℕ
--         carry = (Fin.toℕ remainder ⊓ 1) + quotient
--
--
--         dividend≤carry*base-prim : {remainder : Fin base}
--             → dividend ≡ Fin.toℕ remainder + quotient * base
--             → dividend ≤ (Fin.toℕ remainder ⊓ 1 + quotient) * base
--         dividend≤carry*base-prim {z} prop = {!   !}
--         dividend≤carry*base-prim {s r} prop = {!   !}
--             -- start
--             --     dividend
--             -- ≈⟨ prop ⟩
--             --     Fin.toℕ (s r) + quotient * base
--             -- ≤⟨ +n-mono (quotient * base) (bounded r) ⟩
--             --     suc b + quotient * base
--             -- ≤⟨ +n-mono (quotient * base) (s≤s (m≤n+m b (suc zero))) ⟩
--             --     base + quotient * base
--             -- ≤⟨ *n-mono base (s≤s (m≤n+m quotient (Fin.toℕ r ⊓ 0))) ⟩
--             --     suc (Fin.toℕ r ⊓ 0 + quotient) * base
--             -- ≈⟨ refl ⟩
--             --     (Fin.toℕ (s r) ⊓ 1 + quotient) * base
--             -- □
--         dividend≤carry*base : dividend ≤ carry * base
--         dividend≤carry*base = dividend≤carry*base-prim {remainder} {!   !}
--
--
--         carry-lower-bound : carry ≥ o
--         carry-lower-bound = *n-mono-inverse (suc b) $
--             start
--                 o * base
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 dividend
--             ≤⟨ dividend≤carry*base ⟩
--                 ((Fin.toℕ remainder ⊓ 1) + quotient) * base
--             □
--
--
--         -- carry-upper-bound-prim : {remainder : Fin base}
--         --     → dividend ≡ Fin.toℕ remainder + quotient * base
--         --     → (Fin.toℕ remainder ⊓ 1) + quotient ≤ d + o
--         -- carry-upper-bound-prim {z} prop =
--         --     start
--         --         quotient
--         --     ≤⟨ m≤m*1+n quotient (suc b) ⟩
--         --         quotient * base
--         --     ≈⟨ sym prop ⟩
--         --         dividend
--         --     ≤⟨ dividend-upper-bound ⟩
--         --         d + o
--         --     □
--         -- carry-upper-bound-prim {s r} prop =
--         --     start
--         --         (Fin.toℕ (s r) ⊓ 1) + quotient
--         --     ≤⟨ +n-mono quotient (m⊓n≤m (Fin.toℕ (s r)) 1) ⟩
--         --         Fin.toℕ (s r) + quotient
--         --     ≤⟨ n+-mono (Fin.toℕ (s r)) (m≤m*1+n quotient (suc b)) ⟩
--         --         Fin.toℕ (s r) + quotient * base
--         --     ≈⟨ sym prop ⟩
--         --         dividend
--         --     ≤⟨ dividend-upper-bound ⟩
--         --         d + o
--         --     □
--         carry-upper-bound : carry ≤ d + o
--         -- carry-upper-bound = carry-upper-bound-prim {remainder} {!   !}
--         carry-upper-bound =
--             start
--                 Fin.toℕ remainder ⊓ 1 + quotient
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             □
--         -- carry*base≤sum : carry * base ≤ sum o y (lsd xs)
--         -- carry*base≤sum =
--         --     start
--         --         carry * base
--         --     ≈⟨ refl ⟩
--         --         -- base + quotient * base
--         --     ≤⟨ {!   !} ⟩
--         --         {!   !}
--         --     ≤⟨ {!   !} ⟩
--         --         {!   !}
--         --     ≈⟨ {!   !} ⟩
--         --         {!   !}
--         --     -- ≈⟨ cong (λ w → Fin.toℕ remainder + quotient * base + w) (sym {! lemma ¬gapped  !}) ⟩
--         --     ≤⟨ {!   !} ⟩
--         --         {!   !}
--         --     -- ≈⟨ sym (+-assoc (Fin.toℕ remainder) (quotient * base) {!   !}) ⟩
--         --     --     Fin.toℕ remainder + quotient * base + o * base
--         --     -- ≤⟨ n+-mono (Fin.toℕ remainder + quotient * base) (lemma ¬gapped) ⟩
--         --         Fin.toℕ remainder + quotient * base + (d + o)
--         --     ≈⟨ cong (λ w → w + (d + o)) (sym divModProp) ⟩
--         --         sum o y (lsd xs) ∸ (d + o) + (d + o)
--         --     ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
--         --         sum o y (lsd xs)
--         --     □
--
--
--         -- leftover
--         leftover : ℕ
--
--         leftover = sum o y (lsd xs) ∸ carry * base
--         leftover-lower-bound-prim : {remainder : Fin base}
--             → (prop : sum o y (lsd xs) ≡ Fin.toℕ remainder + quotient * base + (d + o))
--             → sum o y (lsd xs) ∸ ((Fin.toℕ remainder ⊓ 1) + quotient) * base ≥ o
--         leftover-lower-bound-prim {z} prop =
--             start
--                 o
--             ≤⟨ m≤n+m o d ⟩
--                 d + o
--             ≈⟨ sym (m+n∸n≡m (d + o) (quotient * base)) ⟩
--                 d + o + quotient * base ∸ quotient * base
--             ≈⟨ cong (λ w → w ∸ quotient * base) (+-comm (d + o) (quotient * base)) ⟩
--                 quotient * base + (d + o) ∸ quotient * base
--             ≈⟨ cong (λ w → w ∸ quotient * base) (sym prop) ⟩
--                 sum o y (lsd xs) ∸ quotient * base
--             □
--         leftover-lower-bound-prim {s r} prop =
--             let
--                 carry = Fin.toℕ (s r) ⊓ 1 + quotient
--             in
--             start
--                 o
--             ≤⟨ m≤n+m o (Fin.toℕ r) ⟩
--                 Fin.toℕ r + o
--             ≤⟨ m≤m+n (Fin.toℕ r + o) (0 * base) ⟩
--                 Fin.toℕ r + o + 0 * base
--             ≈⟨ cong (λ w → Fin.toℕ r + o + w * base) (sym (n∸n≡0 (suc quotient))) ⟩
--                 Fin.toℕ r + o + (suc quotient ∸ suc quotient) * base
--             ≤⟨ n+-mono (Fin.toℕ r + o)
--                 (*n-mono base
--                     (∸-mono
--                         {1 + quotient}
--                         {quotient + (1 ⊔ o)}
--                         {1 + quotient}
--                         {Fin.toℕ (s r) ⊓ 1 + quotient}
--                         (start
--                             suc quotient
--                         ≈⟨ +-comm 1 quotient ⟩
--                             quotient + 1
--                         ≤⟨ n+-mono quotient (m≤m⊔n 1 o) ⟩
--                             quotient + (1 ⊔ o)
--                         □)
--                         (start
--                             Fin.toℕ (s r) ⊓ 1 + quotient
--                         ≤⟨ +n-mono quotient (m⊓n≤n (Fin.toℕ (s r)) 1) ⟩
--                             suc quotient
--                         □)))
--             ⟩
--                 Fin.toℕ r + o + (quotient + (1 ⊔ o) ∸ (Fin.toℕ (s r) ⊓ 1 + quotient)) * base
--             ≈⟨ cong (λ w → Fin.toℕ r + o + w) (*-distrib-∸ʳ base (quotient + (1 ⊔ o)) carry) ⟩
--                 Fin.toℕ r + o + ((quotient + (1 ⊔ o)) * base ∸ carry * base)
--             ≈⟨ sym (+-∸-assoc (Fin.toℕ r + o) $ *n-mono base $
--                 start
--                     carry
--                 ≈⟨ refl ⟩
--                     Fin.toℕ (s r) ⊓ 1 + quotient
--                 ≤⟨ +n-mono quotient (m⊓n≤n (Fin.toℕ (s r)) 1) ⟩
--                     1 + quotient
--                 ≈⟨ +-comm 1 quotient ⟩
--                     quotient + 1
--                 ≤⟨ n+-mono quotient (m≤m⊔n 1 o) ⟩
--                     quotient + (1 ⊔ o)
--                 □
--             ) ⟩
--                 Fin.toℕ r + o + (quotient + (1 ⊔ o)) * base ∸ carry * base
--             ≈⟨ cong (λ w → w ∸ carry * base) ([a+b]+c≡[a+c]+b (Fin.toℕ r) o ((quotient + (1 ⊔ o)) * base)) ⟩
--                 Fin.toℕ r + (quotient + (1 ⊔ o)) * base + o ∸ carry * base
--             ≈⟨ cong (λ w → Fin.toℕ r + w + o ∸ carry * base) (distribʳ-*-+ base quotient (1 ⊔ o)) ⟩
--                 Fin.toℕ r + (quotient * base + (1 ⊔ o) * base) + o ∸ carry * base
--             ≈⟨ cong (λ w → w + o ∸ carry * base) (sym (+-assoc (Fin.toℕ r) (quotient * base) ((1 ⊔ o) * base))) ⟩
--                 Fin.toℕ r + quotient * base + (1 ⊔ o) * base + o ∸ carry * base
--             ≈⟨ cong (λ w → w ∸ carry * base) (+-assoc (Fin.toℕ r + quotient * base) ((1 ⊔ o) * base) o) ⟩
--                 (Fin.toℕ r + quotient * base) + ((1 ⊔ o) * base + o) ∸ carry * base
--             ≤⟨ ∸n-mono (carry * base) (n+-mono (Fin.toℕ r + quotient * base) (+n-mono o ¬gapped)) ⟩
--                 (Fin.toℕ r + quotient * base) + (suc d + o) ∸ carry * base
--             ≈⟨ cong (λ w → w ∸ carry * base) (+-suc (Fin.toℕ r + quotient * base) (d + o)) ⟩
--                 (suc (Fin.toℕ r + quotient * base) + (d + o)) ∸ carry * base
--             ≈⟨ refl ⟩
--                 (Fin.toℕ (s r) + quotient * base + (d + o)) ∸ carry * base
--             ≈⟨ cong (λ w → w ∸ carry * base) (sym prop) ⟩
--                 sum o y (lsd xs) ∸ carry * base
--             □
--
--         leftover-lower-bound : leftover ≥ o
--         leftover-lower-bound = leftover-lower-bound-prim {remainder} divModProp'
--
--         leftover-upper-bound : leftover ≤ d + o
--         leftover-upper-bound = {!   !}
--             -- start
--             --     sum o y (lsd xs) ∸ (Fin.toℕ remainder ⊓ 1 + quotient) * base
--             -- ≤⟨ n∸-mono (sum o y (lsd xs)) dividend≤carry*base ⟩
--             --     sum o y (lsd xs) ∸ dividend
--             -- ≈⟨ cong (λ w → sum o y (lsd xs) ∸ w) divModProp ⟩
--             --     sum o y (lsd xs) ∸ (Fin.toℕ remainder + quotient * base)
--             -- ≈⟨ cong (λ w → w ∸ (Fin.toℕ remainder + quotient * base)) divModProp' ⟩
--             --     Fin.toℕ remainder + quotient * base + (d + o) ∸ (Fin.toℕ remainder + quotient * base)
--             -- ≈⟨ cong (λ w → w ∸ (Fin.toℕ remainder + quotient * base)) (+-comm (Fin.toℕ remainder + quotient * base) (d + o)) ⟩
--             --     d + o + (Fin.toℕ remainder + quotient * base) ∸ (Fin.toℕ remainder + quotient * base)
--             -- ≈⟨ m+n∸n≡m (d + o) (Fin.toℕ remainder + quotient * base) ⟩
--             --     d + o
--             -- □
--
--         property :
--                  Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
--             +   (Digit-toℕ (Digit-fromℕ carry    o carry-upper-bound) o) * base
--             ≡   sum o y (lsd xs)
--         property =
--             begin
--                 Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o +
--                 Digit-toℕ (Digit-fromℕ carry    o carry-upper-bound) o * base
--             ≡⟨ cong₂
--                 (λ r c → r + c * base)
--                 (Digit-toℕ-fromℕ leftover leftover-lower-bound leftover-upper-bound)
--                 (Digit-toℕ-fromℕ carry carry-lower-bound carry-upper-bound)
--             ⟩
--                 leftover + carry * base
--             ≡⟨ {!   !} ⟩
--                 {!   !}
--             ≡⟨ {!   !} ⟩
--                 {!   !}
--             ≡⟨ {!   !} ⟩
--                 sum o y (lsd xs)
--             ≡⟨ refl ⟩
--                 sum o y (lsd xs)
--             ∎

-- data Sum : (b d o : ℕ) (y x : Digit (suc d)) → Set where
--     Before : ∀ {b d o y x}
--         → (leftover : Digit (suc d))
--         → (property : Digit-toℕ leftover o ≡ sum o y x)
--         → Sum b d o y x
--     Between : ∀ {b d o y x}
--         → (leftover carry : Digit (suc d))
--         → (property : Digit-toℕ leftover o + (Digit-toℕ carry o) * suc b ≡ sum o y x)
--         → Sum b d o y x
--     After : ∀ {b d o y x}
--         → (leftover carry : Digit (suc d))
--         → (property : Digit-toℕ leftover o + (Digit-toℕ carry o) * suc b ≡ sum o y x)
--         → Sum b d o y x
--
-- sumView : ∀ b d o
--     → (cont : True (Continuous? (suc b) (suc d) o))
--     → (proper : suc d + o ≥ 2)
--     → (y : Digit (suc d))
--     → (xs : Num (suc b) (suc d) o)
--     → Sum b d o y (lsd xs)
-- sumView b d o cont proper y xs with (sum o y (lsd xs)) ≤? d + o
-- sumView b d o cont proper y xs | yes p
--     = Before
--         (Digit-fromℕ (sum o y (lsd xs)) o leftover-upper-bound)
--         property
--     where
--         leftover : ℕ
--         leftover = sum o y (lsd xs)
--
--         leftover-upper-bound : leftover ≤ d + o
--         leftover-upper-bound = p
--
--         property :
--               Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
--             ≡ sum o y (lsd xs)
--         property =
--             begin
--                 Digit-toℕ (Digit-fromℕ (sum o y (lsd xs)) o p) o
--             ≡⟨ Digit-toℕ-fromℕ (sum o y (lsd xs)) (sum≥o o y (lsd xs)) p ⟩
--                 sum o y (lsd xs)
--             ∎
--
-- sumView b d o cont proper y xs | no ¬p with (sum o y (lsd xs)) ≤? o + (1 ⊔ o) * suc b
-- sumView b d o cont proper y xs | no ¬p | yes q
--     = Between
--         (Digit-fromℕ leftover o leftover-upper-bound)
--         (Digit-fromℕ carry     o carry-upper-bound)
--         property
--     where
--         sum≥carried : sum o y (lsd xs) ≥ (1 ⊔ o) * suc b
--         sum≥carried =
--                 start
--                     (1 ⊔ o) * suc b
--                 ≤⟨ ≤-pred (≰⇒> (Continuous⇒¬Gapped#0 cont proper)) ⟩
--                     suc d
--                 ≤⟨ s≤s (m≤m+n d o) ⟩
--                     suc (d + o)
--                 ≤⟨ ≰⇒> ¬p ⟩
--                     sum o y (lsd xs)
--                 □
--         leftover : ℕ
--         leftover = sum o y (lsd xs) ∸ (1 ⊔ o) * suc b
--
--         leftover-lower-bound : leftover ≥ o
--         leftover-lower-bound = +n-mono-inverse ((1 ⊔ o) * suc b) $
--             start
--                 o + (1 ⊔ o) * suc b
--             ≤⟨ n+-mono o (≤-pred $ ≰⇒> (Continuous⇒¬Gapped#0 cont proper)) ⟩
--                 o + suc d
--             ≈⟨ +-comm o (suc d) ⟩
--                 suc (d + o)
--             ≤⟨ ≰⇒> ¬p ⟩
--                 sum o y (lsd xs)
--             ≈⟨ sym (m∸n+n≡m sum≥carried) ⟩
--                 leftover + (1 ⊔ o) * suc b
--             □
--
--         leftover-upper-bound : leftover ≤ d + o
--         leftover-upper-bound = +n-mono-inverse ((1 ⊔ o) * suc b) $
--             start
--                 sum o y (lsd xs) ∸ (1 ⊔ o) * suc b + (1 ⊔ o) * suc b
--             ≈⟨ m∸n+n≡m sum≥carried ⟩
--                 sum o y (lsd xs)
--             ≤⟨ q ⟩
--                 o + (1 ⊔ o) * suc b
--             ≤⟨ m≤n+m (o + (1 ⊔ o) * suc b) d ⟩
--                 d + (o + (1 ⊔ o) * suc b)
--             ≈⟨ sym (+-assoc d o ((1 ⊔ o) * suc b)) ⟩
--                 d + o + (1 ⊔ o) * suc b
--             □
--
--         carry : ℕ
--         carry = 1 ⊔ o
--
--         carry-lower-bound : carry ≥ o
--         carry-lower-bound =
--             start
--                 o
--             ≤⟨ m≤m⊔n o 1 ⟩
--                 o ⊔ 1
--             ≈⟨ ⊔-comm o 1 ⟩
--                 1 ⊔ o
--             □
--
--         carry-upper-bound : carry ≤ d + o
--         carry-upper-bound = ⊔-upper-bound d o 1 (≤-pred proper)
--
--         property :
--               Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
--             + Digit-toℕ (Digit-fromℕ carry o carry-upper-bound) o * suc b
--             ≡ sum o y (lsd xs)
--         property =
--             begin
--                 Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o +
--                 Digit-toℕ (Digit-fromℕ carry o carry-upper-bound) o * suc b
--             ≡⟨ cong₂
--                 (λ r c → r + c * suc b)
--                 (Digit-toℕ-fromℕ leftover leftover-lower-bound leftover-upper-bound)
--                 (Digit-toℕ-fromℕ carry carry-lower-bound carry-upper-bound)
--             ⟩
--                 leftover + carry * suc b
--             ≡⟨ refl ⟩
--                 sum o y (lsd xs) ∸ (1 ⊔ o) * suc b + (1 ⊔ o) * suc b
--             ≡⟨ m∸n+n≡m sum≥carried ⟩
--                 sum o y (lsd xs)
--             ∎
-- sumView b d o cont proper y xs | no ¬p | no ¬q = {!   !}
--
-- n+-Proper : ∀ {b d o}
--     → (cont : True (Continuous? (suc b) (suc d) o))
--     → (proper : suc d + o ≥ 2)
--     → (y : Digit (suc d))
--     → (xs : Num (suc b) (suc d) o)
--     → Num (suc b) (suc d) o
-- n+-Proper {b} {d} {o} cont proper y xs with sumView b d o cont proper y xs
-- n+-Proper cont proper y (x ∙)    | Before leftover property = leftover ∙
-- n+-Proper cont proper y (x ∷ xs) | Before leftover property = leftover ∷ xs
-- n+-Proper cont proper y (x ∙)    | Between leftover carry property = leftover ∷ carry ∙
-- n+-Proper cont proper y (x ∷ xs) | Between leftover carry property = leftover ∷ n+-Proper cont proper carry xs
-- n+-Proper cont proper y xs | After leftover carry property = {!   !}
--
--
-- n+-Proper-toℕ : ∀ {b d o}
--     → (cont : True (Continuous? (suc b) (suc d) o))
--     → (proper : suc d + o ≥ 2)
--     → (y : Digit (suc d))
--     → (xs : Num (suc b) (suc d) o)
--     → ⟦ n+-Proper cont proper y xs ⟧ ≡ Digit-toℕ y o + ⟦ xs ⟧
-- n+-Proper-toℕ {b} {d} {o} cont proper y xs with sumView b d o cont proper y xs
-- n+-Proper-toℕ {b} {d} {o} cont proper y (x ∙) | Before leftover property = property
-- n+-Proper-toℕ {b} {d} {o} cont proper y (x ∷ xs) | Before leftover property =
--     begin
--         Digit-toℕ leftover o + ⟦ xs ⟧ * suc b
--     ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) property ⟩
--         sum o y x + ⟦ xs ⟧ * suc b
--     ≡⟨ +-assoc (Digit-toℕ y o) (Digit-toℕ x o) (⟦ xs ⟧ * suc b) ⟩
--         Digit-toℕ y o + (Digit-toℕ x o + ⟦ xs ⟧ * suc b)
--     ∎
-- n+-Proper-toℕ {b} {d} {o} cont proper y (x ∙) | Between leftover carry property = property
-- n+-Proper-toℕ {b} {d} {o} cont proper y (x ∷ xs) | Between leftover carry property =
--     begin
--         Digit-toℕ leftover o + ⟦ n+-Proper cont proper carry xs ⟧ * suc b
--     ≡⟨ cong (λ w → Digit-toℕ leftover o + w * suc b) (n+-Proper-toℕ cont proper carry xs) ⟩
--         Digit-toℕ leftover o + (Digit-toℕ carry o + ⟦ xs ⟧) * suc b
--     ≡⟨ cong (λ w → Digit-toℕ leftover o + w) (distribʳ-*-+ (suc b) (Digit-toℕ carry o) ⟦ xs ⟧) ⟩
--         Digit-toℕ leftover o + (Digit-toℕ carry o * suc b + ⟦ xs ⟧ * suc b)
--     ≡⟨ sym (+-assoc (Digit-toℕ leftover o) (Digit-toℕ carry o * suc b) (⟦ xs ⟧ * suc b)) ⟩
--         Digit-toℕ leftover o + Digit-toℕ carry o * suc b + ⟦ xs ⟧ * suc b
--     ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) property ⟩
--         sum o y x + ⟦ xs ⟧ * suc b
--     ≡⟨ +-assoc (Digit-toℕ y o) (Digit-toℕ x o) (⟦ xs ⟧ * suc b) ⟩
--         Digit-toℕ y o + ⟦ x ∷ xs ⟧
--     ∎
-- n+-Proper-toℕ {b} {d} {o} cont proper y xs | After leftover carry property = {!   !}
