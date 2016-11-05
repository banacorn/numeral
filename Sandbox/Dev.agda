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
    → (y x : Digit (suc d))
    → ℕ
sum o y x = Digit-toℕ y o + Digit-toℕ x o

sum≥o : ∀ {d} o
    → (y x : Digit (suc d))
    → sum o y x ≥ o
sum≥o o y x = start
        o
    ≤⟨ m≤n+m o (Fin.toℕ y) ⟩
        Digit-toℕ y o
    ≤⟨ m≤m+n (Digit-toℕ y o) (Digit-toℕ x o) ⟩
        sum o y x
    □

sum-upper-bound : ∀ {d} o
    → (y x : Digit (suc d))
    → sum o y x ≤ (d + o) + (d + o)
sum-upper-bound {d} o y x =
    start
        Digit-toℕ y o + Digit-toℕ x o
    ≤⟨ ≤-pred (Digit<d+o y o) +-mono ≤-pred (Digit<d+o x o) ⟩
        d + o + (d + o)
    □

--
--  When the sum is over d + o, but still within the "buffer capacity"
--
--  0   o                d+o          d+o+(1⊔o)×b
----|---|-----------------|----------------|
--    o          d              (1⊔o)×b
--                        [----------------] "buffer capacity"
--
--  |---------------------------------| sum
--
--                    |---------------| carry
--  |-----------------|                 leftover
--
--
--  When the sum is over d + o and exceeds the "buffer capacity"
--
--  0   o                d+o          d+o+(1⊔o)×b
----|---|-----------------|----------------|
--    o          d              (1⊔o)×b
--                        [----------------] "buffer capacity"
--
--  |----------------------------------------------| sum
--                        |------------------------| dividend = sum-d-o
--                      |==------------------------| carry = [dividend/b+1]×b
--  |-------------------|                            leftover = sum - carry



data Sum : (b d o : ℕ) (y x : Digit (suc d)) → Set where
    NeedNoCarry : ∀ {b d o y x}
        → (leftover : Digit (suc d))
        → (property : Digit-toℕ leftover o ≡ sum o y x)
        → Sum b d o y x
    Carried : ∀ {b d o y x}
        → (leftover carry : Digit (suc d))
        → (property : Digit-toℕ leftover o + (Digit-toℕ carry o) * suc (suc b) ≡ sum o y x)
        → Sum b d o y x

sumView : ∀ b d o
    → (¬gapped : (1 ⊔ o) * suc (suc b) ≤ suc d)
    → (proper : suc d + o ≥ 2)
    → (y : Digit (suc d))
    → (xs : Num (suc (suc b)) (suc d) o)
    → Sum b d o y (lsd xs)
sumView b d o ¬gapped proper y xs with (sum o y (lsd xs)) ≤? d + o
sumView b d o ¬gapped proper y xs | yes p
    = NeedNoCarry
        (Digit-fromℕ (sum o y (lsd xs)) o leftover-upper-bound)
        property
    where
        leftover : ℕ
        leftover = sum o y (lsd xs)

        leftover-upper-bound : leftover ≤ d + o
        leftover-upper-bound = p

        property :
              Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
            ≡ sum o y (lsd xs)
        property =
            begin
                Digit-toℕ (Digit-fromℕ (sum o y (lsd xs)) o p) o
            ≡⟨ Digit-toℕ-fromℕ (sum o y (lsd xs)) (sum≥o o y (lsd xs)) p ⟩
                sum o y (lsd xs)
            ∎
sumView b d o ¬gapped proper y xs | no ¬p with _divMod_ (sum o y (lsd xs) ∸ (d + o)) (suc (suc b))
sumView b d o ¬gapped proper y xs | no ¬p | result quotient remainder divModProp _ _
    = Carried
        (Digit-fromℕ leftover o leftover-upper-bound)
        (Digit-fromℕ carry o carry-upper-bound)
        property
    where

        base : ℕ
        base = suc (suc b)

        -- leftover + carry * suc (suc b) ≡ sum




        -- lemma : ∀ {o}
        --     → (1 ⊔ o) * base ≤ suc d
        --     → d + o ≥ base
        -- lemma {zero} ¬gapped = ≤-pred $
        --     start
        --         {!suc base  !}
        --     ≤⟨ {!   !} ⟩
        --         {!   !}
        --     ≤⟨ {!   !} ⟩
        --         {!   !}
        --     ≤⟨ {!   !} ⟩
        --         base + 0
        --     ≤⟨ ¬gapped ⟩
        --         suc d
        --     ≈⟨ sym (+-right-identity (suc d))⟩
        --         suc d + zero
        --     □
        -- lemma {suc o} ¬gapped = {!   !}
            -- start
            --     suc base
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≤⟨ {!   !} ⟩
            --     (1 ⊔ o) * base
            -- ≤⟨ m≤m+n ((1 ⊔ o) * base) o ⟩
            --     (1 ⊔ o) * base + o
            -- ≤⟨ +n-mono o ¬gapped ⟩
            --     suc (d + o)
            -- □
        -- lemma {zero} ¬gapped =
        --     -- start
        --     --     zero
        --     -- ≤⟨ z≤n ⟩
        --     --     d
        --     -- ≈⟨ sym (+-right-identity d)⟩
        --     --     d + zero
        --     -- □
        -- lemma {suc o} ¬gapped =
        --     start
        --         suc o * base
        --     ≤⟨ m≤m+n (suc o * base) o ⟩
        --         suc o * base + o
        --     ≈⟨ sym (+-suc (suc (b + o * base)) o) ⟩
        --         suc (b + o * base + suc o)
        --     ≤⟨ +n-mono (suc o) (≤-pred ¬gapped) ⟩
        --         d + suc o
        --     □

        -- dividend
        dividend : ℕ
        dividend = sum o y (lsd xs) ∸ (d + o)

        dividend-upper-bound : dividend ≤ d + o
        dividend-upper-bound = +n-mono-inverse (d + o) $
            start
                sum o y (lsd xs) ∸ (d + o) + (d + o)
            ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
                sum o y (lsd xs)
            ≤⟨ sum-upper-bound o y (lsd xs) ⟩
                d + o + (d + o)
            □


        divModProp' : sum o y (lsd xs) ≡ Fin.toℕ remainder + quotient * base + (d + o)
        divModProp' = cancel-∸-right (d + o) (<⇒≤ (≰⇒> ¬p)) (m≤n+m (d + o) (Fin.toℕ remainder + quotient * base)) $
            begin
                sum o y (lsd xs) ∸ (d + o)
            ≡⟨ refl ⟩
                dividend
            ≡⟨ divModProp ⟩
                Fin.toℕ remainder + quotient * base
            ≡⟨ sym (m+n∸n≡m (Fin.toℕ remainder + quotient * base) (d + o)) ⟩
                Fin.toℕ remainder + quotient * base + (d + o) ∸ (d + o)
            ∎


        -- carry
        carry : ℕ
        carry = (Fin.toℕ remainder ⊓ 1) + quotient

        -- carry-upper-bound-prim : ∀ q
        --     → dividend ≡ Fin.toℕ remainder + q * base
        --     → suc q ≤ d + o
        -- carry-upper-bound-prim zero prop = ≤-pred proper
        -- carry-upper-bound-prim (suc q) prop =
        --     start
        --         suc (suc q)
        --     ≤⟨ s≤s (m≤n+m (suc q) (q * suc zero)) ⟩
        --         suc (q * suc zero + suc q)
        --     ≤⟨ n+-mono (suc q * 1) (m≤m*1+n (suc q) b) ⟩
        --         suc q * 1 + suc q * suc b
        --     ≈⟨ sym (distrib-left-*-+ (suc q) 1 (suc b)) ⟩
        --         suc q * base
        --     ≤⟨ m≤n+m (suc q * base) (Fin.toℕ remainder) ⟩
        --         Fin.toℕ remainder + suc q * base
        --     ≈⟨ sym prop ⟩
        --         dividend
        --     ≤⟨ dividend-upper-bound ⟩
        --         d + o
        --     □

        carry-upper-bound-prim : {remainder : Fin base}
            → dividend ≡ Fin.toℕ remainder + quotient * base
            → (Fin.toℕ remainder ⊓ 1) + quotient ≤ d + o
        carry-upper-bound-prim {z} prop =
            start
                quotient
            ≤⟨ m≤m*1+n quotient (suc b) ⟩
                quotient * base
            ≈⟨ sym prop ⟩
                dividend
            ≤⟨ dividend-upper-bound ⟩
                d + o
            □
        carry-upper-bound-prim {s r} prop =
            start
                (Fin.toℕ (s r) ⊓ 1) + quotient
            ≤⟨ +n-mono quotient (m⊓n≤m (Fin.toℕ (s r)) 1) ⟩
                Fin.toℕ (s r) + quotient
            ≤⟨ n+-mono (Fin.toℕ (s r)) (m≤m*1+n quotient (suc b)) ⟩
                Fin.toℕ (s r) + quotient * base
            ≈⟨ sym prop ⟩
                dividend
            ≤⟨ dividend-upper-bound ⟩
                d + o
            □
        carry-upper-bound : carry ≤ d + o
        carry-upper-bound = carry-upper-bound-prim {remainder} divModProp
        -- carry*base≤sum : carry * base ≤ sum o y (lsd xs)
        -- carry*base≤sum =
        --     start
        --         carry * base
        --     ≈⟨ refl ⟩
        --         -- base + quotient * base
        --     ≤⟨ {!   !} ⟩
        --         {!   !}
        --     ≤⟨ {!   !} ⟩
        --         {!   !}
        --     ≈⟨ {!   !} ⟩
        --         {!   !}
        --     -- ≈⟨ cong (λ w → Fin.toℕ remainder + quotient * base + w) (sym {! lemma ¬gapped  !}) ⟩
        --     ≤⟨ {!   !} ⟩
        --         {!   !}
        --     -- ≈⟨ sym (+-assoc (Fin.toℕ remainder) (quotient * base) {!   !}) ⟩
        --     --     Fin.toℕ remainder + quotient * base + o * base
        --     -- ≤⟨ n+-mono (Fin.toℕ remainder + quotient * base) (lemma ¬gapped) ⟩
        --         Fin.toℕ remainder + quotient * base + (d + o)
        --     ≈⟨ cong (λ w → w + (d + o)) (sym divModProp) ⟩
        --         sum o y (lsd xs) ∸ (d + o) + (d + o)
        --     ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
        --         sum o y (lsd xs)
        --     □


        -- leftover
        leftover : ℕ
        leftover = sum o y (lsd xs) ∸ carry * base

        leftover-lower-bound-prim : {remainder : Fin base}
            → (prop : sum o y (lsd xs) ≡ Fin.toℕ remainder + quotient * base + (d + o))
            → sum o y (lsd xs) ∸ ((Fin.toℕ remainder ⊓ 1) + quotient) * base ≥ o
        leftover-lower-bound-prim {z} prop =
            start
                o
            ≤⟨ m≤n+m o d ⟩
                d + o
            ≈⟨ sym (m+n∸n≡m (d + o) (quotient * base)) ⟩
                d + o + quotient * base ∸ quotient * base
            ≈⟨ cong (λ w → w ∸ quotient * base) (+-comm (d + o) (quotient * base)) ⟩
                quotient * base + (d + o) ∸ quotient * base
            ≈⟨ cong (λ w → w ∸ quotient * base) (sym prop) ⟩
                sum o y (lsd xs) ∸ quotient * base
            □
        leftover-lower-bound-prim {s r} prop =
            let
                carry = Fin.toℕ (s r) ⊓ 1 + quotient
            in
            start
                o
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                {!  !}
            ≈⟨ {!   !} ⟩
                {!   !}
            ≈⟨ sym (+-∸-assoc (Fin.toℕ r + o) $ *n-mono base $
                start
                    carry
                ≈⟨ refl ⟩
                    Fin.toℕ (s r) ⊓ 1 + quotient
                ≤⟨ +n-mono quotient {!  !} ⟩
                    {!   !}
                ≤⟨ {!   !} ⟩
                    {!   !}
                ≤⟨ {!   !} ⟩
                    quotient + (1 ⊔ o)
                □
            ) ⟩
                Fin.toℕ r + o + (quotient + (1 ⊔ o)) * base ∸ carry * base
            ≈⟨ cong (λ w → w ∸ carry * base) ([a+b]+c≡[a+c]+b (Fin.toℕ r) o ((quotient + (1 ⊔ o)) * base)) ⟩
                Fin.toℕ r + (quotient + (1 ⊔ o)) * base + o ∸ carry * base
            ≈⟨ cong (λ w → Fin.toℕ r + w + o ∸ carry * base) (distribʳ-*-+ base quotient (1 ⊔ o)) ⟩
                Fin.toℕ r + (quotient * base + (1 ⊔ o) * base) + o ∸ carry * base
            ≈⟨ cong (λ w → w + o ∸ carry * base) (sym (+-assoc (Fin.toℕ r) (quotient * base) ((1 ⊔ o) * base))) ⟩
                Fin.toℕ r + quotient * base + (1 ⊔ o) * base + o ∸ carry * base
            ≈⟨ cong (λ w → w ∸ carry * base) (+-assoc (Fin.toℕ r + quotient * base) ((1 ⊔ o) * base) o) ⟩
                (Fin.toℕ r + quotient * base) + ((1 ⊔ o) * base + o) ∸ carry * base
            ≤⟨ ∸n-mono (carry * base) (n+-mono (Fin.toℕ r + quotient * base) (+n-mono o ¬gapped)) ⟩
                (Fin.toℕ r + quotient * base) + (suc d + o) ∸ carry * base
            ≈⟨ cong (λ w → w ∸ carry * base) (+-suc (Fin.toℕ r + quotient * base) (d + o)) ⟩
                (suc (Fin.toℕ r + quotient * base) + (d + o)) ∸ carry * base
            ≈⟨ refl ⟩
            --     -- {!   !}
            -- -- ≈⟨ sym (m+n∸n≡m {!   !} {!   !}) ⟩
            --     (Fin.toℕ (s r) ⊓ 1 + quotient * base + (d + o)) ∸ (Fin.toℕ (s r) ⊓ 1 + quotient) * base
            -- ≤⟨ ∸n-mono (carry * base)
            --     (+n-mono (d + o)
            --         (+n-mono (quotient * base) (m⊓n≤m (Fin.toℕ (s r)) 1))) ⟩
                (Fin.toℕ (s r) + quotient * base + (d + o)) ∸ carry * base
            ≈⟨ cong (λ w → w ∸ carry * base) (sym prop) ⟩
                sum o y (lsd xs) ∸ carry * base
            □

        leftover-lower-bound : leftover ≥ o
        leftover-lower-bound = leftover-lower-bound-prim {remainder} divModProp'

            -- start
            --     o
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≤⟨ {!   !} ⟩
            --     {!  !}
            -- ≈⟨ {!   !} ⟩
            --     {!   !}
            -- ≈⟨ {!   !} ⟩
            --     Fin.toℕ remainder + quotient * base + (d + o) ∸ carry * base
            -- ≈⟨ cong (λ w → w ∸ carry * base) (sym divModProp') ⟩
            --     leftover
            -- □
        -- leftover-lower-bound = +n-mono-inverse (suc quotient * base) $ ≤-pred $
        --     start
        --         suc o + suc quotient * base
        --     -- ≤⟨ n+-mono (suc o) (*n-mono (base) carry-upper-bound) ⟩
        --     --     suc o + (d + o) * base
        --     ≤⟨ {!   !} ⟩
        --         {!   !}
        --     ≤⟨ {!   !} ⟩
        --         {!   !}
        --     ≈⟨ {!   !} ⟩
        --         {!   !}
        --     ≈⟨ {!   !} ⟩
        --         {!   !}
        --     ≈⟨ {!   !} ⟩
        --         Fin.toℕ remainder + ((quotient + 1) * base + o)
        --     ≈⟨ cong (λ w → Fin.toℕ remainder + (w + o)) (distribʳ-*-+ (base) quotient 1) ⟩
        --         Fin.toℕ remainder + (quotient * base + 1 * base + o)
        --     ≈⟨ cong (λ w → Fin.toℕ remainder + w) (+-assoc (quotient * base) (1 * base) o) ⟩
        --         Fin.toℕ remainder + (quotient * base + (1 * base + o))
        --     ≈⟨ sym (+-assoc (Fin.toℕ remainder) (quotient * base) (1 * base + o)) ⟩
        --         Fin.toℕ remainder + quotient * base + (1 * base + o)
        --     ≤⟨ n+-mono (Fin.toℕ remainder + quotient * base) (+n-mono o $
        --         start
        --             1 * (base)
        --         ≤⟨ *n-mono (base) (m≤m⊔n 1 o) ⟩
        --             (suc zero ⊔ o) * base
        --         ≤⟨ ¬gapped ⟩
        --             suc d
        --         □
        --     ) ⟩
        --         Fin.toℕ remainder + quotient * base + suc (d + o)
        --     ≈⟨ +-suc (Fin.toℕ remainder + quotient * base) (d + o) ⟩
        --         suc (Fin.toℕ remainder + quotient * base + (d + o))
        --     ≈⟨ cong suc (sym divModProp') ⟩
        --         suc (sum o y (lsd xs))
        --     ≈⟨ cong suc (sym (m∸n+n≡m $
        --         start
        --             suc quotient * base
        --         ≤⟨ *n-mono (base) carry-upper-bound ⟩
        --             (d + o) * base
        --         ≤⟨ *n-mono (base) {!   !} ⟩
        --             _ * base
        --         ≤⟨ {!   !} ⟩
        --             {!   !}
        --         ≤⟨ {!   !} ⟩
        --             sum o y (lsd xs)
        --         □
        --     )) ⟩
        --         suc (leftover + suc quotient * base)
        --     □
            -- start
            --     {!  !}
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≈⟨ {!   !} ⟩
            --     {!   !}
            -- ≈⟨ {!   !} ⟩
            --     {!   !}
            -- ≈⟨ cong (λ w → Fin.toℕ remainder + quotient * base + (w + o) ∸ suc quotient * base) (sym {! lemma  !}) ⟩
            --     Fin.toℕ remainder + quotient * base + (d + o) ∸ suc quotient * base
            -- ≈⟨ cong (λ w → w ∸ carry * base) (sym divModProp') ⟩
            --     leftover
            -- □
            -- +n-mono-inverse (carry * base) $ ≤-pred $
            -- start
            --     suc (o + suc quotient * base)
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≤⟨ {!   !} ⟩
            --     {!   !}
            -- ≤⟨ m≤n+m {!  Fin.toℕ remainder !} {!   !} ⟩
            --     {!   !}
            -- ≈⟨ sym (+-assoc (Fin.toℕ remainder) {!   !} {!   !}) ⟩
            --     suc (Fin.toℕ remainder + quotient * base + (d + o))
            -- ≈⟨ cong suc (sym divModProp') ⟩
            --     suc (sum o y (lsd xs))
            -- ≈⟨ sym (m∸n+n≡m {!   !}) ⟩
            --     suc leftover + carry * base
            -- □


        leftover-upper-bound : leftover ≤ d + o
        leftover-upper-bound = {!   !}
            -- start
            --     sum o y (lsd xs) ∸ suc quotient * base
            -- ≈⟨ cong (λ w → w ∸ suc quotient * base) divModProp' ⟩
            --     Fin.toℕ remainder + quotient * base + (d + o) ∸ suc quotient * base
            -- ≤⟨ ∸n-mono (suc quotient * base)
            --     (+n-mono (d + o)
            --         (+n-mono (quotient * base)
            --             (<⇒≤ (bounded remainder))))
            -- ⟩
            --     ((b + quotient * base) + (d + o)) ∸ (b + quotient * base)
            -- ≈⟨ cong (λ w → w ∸ (b + quotient * base)) (+-comm (b + quotient * base) (d + o)) ⟩
            --     d + o + (b + quotient * base) ∸ (b + quotient * base)
            -- ≈⟨ m+n∸n≡m (d + o) (b + quotient * base) ⟩
            --     d + o
            -- □

        property :
                 Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
            +   (Digit-toℕ (Digit-fromℕ carry    o carry-upper-bound) o) * base
            ≡   sum o y (lsd xs)
        property =
            begin
                Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o +
                Digit-toℕ (Digit-fromℕ carry    o carry-upper-bound) o * base
            ≡⟨ cong₂
                (λ r c → r + c * base)
                (Digit-toℕ-fromℕ leftover {!   !} leftover-upper-bound)
                (Digit-toℕ-fromℕ carry {!   !} carry-upper-bound)
            ⟩
                leftover + carry * base
            ≡⟨ {!   !} ⟩
                {!   !}
            ≡⟨ {!   !} ⟩
                {!   !}
            ≡⟨ {!   !} ⟩
                sum o y (lsd xs)
            ≡⟨ refl ⟩
                sum o y (lsd xs)
            ∎

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
