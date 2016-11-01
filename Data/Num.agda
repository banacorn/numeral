module Data.Num where

open import Data.Num.Core
open import Data.Num.Maximum
open import Data.Num.Bounded
open import Data.Num.Next
open import Data.Num.Incrementable
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

1+ : ∀ {b d o}
    → {cont : True (Continuous? b d o)}
    → (xs : Num b d o)
    → Num b d o
1+ {cont = cont} xs = proj₁ (toWitness cont xs)

1+-toℕ : ∀ {b d o}
    → {cont : True (Continuous? b d o)}
    → (xs : Num b d o)
    → ⟦ 1+ {cont = cont} xs ⟧ ≡ suc ⟦ xs ⟧
1+-toℕ {cont = cont} xs = proj₂ (toWitness cont xs)

sum : ∀ {d}
    → (o : ℕ)
    → (n x : Digit (suc d))
    → ℕ
sum o n x = Digit-toℕ n o + Digit-toℕ x o

sum≥o : ∀ {d} o
    → (n x : Digit (suc d))
    → sum o n x ≥ o
sum≥o o n x = start
        o
    ≤⟨ m≤n+m o (Fin.toℕ n) ⟩
        Digit-toℕ n o
    ≤⟨ m≤m+n (Digit-toℕ n o) (Digit-toℕ x o) ⟩
        sum o n x
    □

sum-upper-bound : ∀ {d} o
    → (n x : Digit (suc d))
    → sum o n x ≤ (d + o) + (d + o)
sum-upper-bound {d} o n x =
    start
        Digit-toℕ n o + Digit-toℕ x o
    ≤⟨ ≤-pred (Digit<d+o n o) +-mono ≤-pred (Digit<d+o x o) ⟩
        d + o + (d + o)
    □

sum-lemma : ∀ {d} o
    → (n x : Digit (suc d))
    → sum (suc o) n x ≡ 2 + sum o n x
sum-lemma o n x =
    begin
        Fin.toℕ n + suc o + (Fin.toℕ x + suc o)
    ≡⟨ cong₂ _+_ (+-suc (Fin.toℕ n) o) (+-suc (Fin.toℕ x) o) ⟩
        suc (Fin.toℕ n + o + suc (Fin.toℕ x + o))
    ≡⟨ cong suc (+-suc (Fin.toℕ n + o) (Fin.toℕ x + o)) ⟩
        suc (suc (Fin.toℕ n + o + (Fin.toℕ x + o)))
    ∎


-- sum-lower-bound' : ∀ {d} o
--     → (n x : Digit (suc d))
--     → sum o n x > d + o
--     → (1 ⊔ o) * 1 ≤ suc d
--     → sum o n x ∸ (d + o) ≥ o
-- sum-lower-bound' {d} o n x p ¬gapped =
--     start
--         o
--     ≤⟨ {!   !} ⟩
--         {!   !}
--     ≤⟨ {!   !} ⟩
--         {!   !}
--     ≤⟨ {!   !} ⟩
--         {!   !}
--     ≤⟨ {!1   !} ⟩
--         Fin.toℕ n + o + (Fin.toℕ x + o) ∸ (d + o)
--     □
-- sum-lower-bound' {d} zero n x p ¬gapped =
--     +n-mono-inverse (d + zero)
--     $ start
--         d + zero
--     ≤⟨ <⇒≤ p ⟩
--         Fin.toℕ n + zero + (Fin.toℕ x + zero)
--     ≈⟨ sym (m∸n+n≡m (<⇒≤ p)) ⟩
--         Fin.toℕ n + zero + (Fin.toℕ x + zero) ∸ (d + zero) + (d + zero)
--     □
-- sum-lower-bound' {d} (suc o) n x p ¬gapped =
--     start
--         suc o
--     ≤⟨ s≤s (sum-lower-bound' o n x {! p'  !} ¬gapped') ⟩
--         suc (sum o n x ∸ (d + o))
--     ≤⟨ {!   !} ⟩
--         {!   !}
--     ≤⟨ {!   !} ⟩
--         {!   !}
--     ≤⟨ {!   !} ⟩
--         Fin.toℕ n + suc o + (Fin.toℕ x + suc o) ∸ (d + suc o)
--     □
--     where
--         p' : sum o n x ≥ d + o
--         p' = n+-mono-inverse 2 $
--             start
--                 2 + (d + o)
--             ≈⟨ cong suc (sym (+-suc d o)) ⟩
--                 suc (d + suc o)
--             ≤⟨ p ⟩
--                 sum (suc o) n x
--             ≈⟨ sum-lemma o n x ⟩
--                 2 + sum o n x
--             □
--         ¬gapped' : (1 ⊔ o) * 1 ≤ suc d
--         ¬gapped' =
--             start
--                 (suc zero ⊔ o) * suc zero
--             ≈⟨ *-right-identity (suc zero ⊔ o) ⟩
--                 suc zero ⊔ o
--             ≤⟨ m⊔n≤m+n (suc zero) o ⟩
--                 suc o
--             ≈⟨ cong suc (sym (*-right-identity o)) ⟩
--                 suc (o * suc zero)
--             ≤⟨ ¬gapped ⟩
--                 suc d
--             □
    -- start
    --     suc o
    -- ≤⟨ s≤s (sum-lower-bound' o n x $
    --     start
    --         d + o
    --     ≈⟨ {!   !} ⟩
    --         {!   !}
    --     ≈⟨ {!   !} ⟩
    --         {!   !}
    --     ≈⟨ {!   !} ⟩
    --         {!   !}
    --     ≈⟨ {! p  !} ⟩
    --         Fin.toℕ n + o + (Fin.toℕ x + o)
    --     □
    -- ) ⟩
    --     {!   !}
    -- ≤⟨ {!   !} ⟩
    --     {!   !}
    -- ≤⟨ {!   !} ⟩
    --     {!   !}
    -- ≤⟨ {!   !} ⟩
    --     Fin.toℕ n + suc o + (Fin.toℕ x + suc o) ∸ (d + suc o)
    -- □

-- Unary
--
--
--  ℕ   0   o       d   o       d
--------|---|-------|---|-------|
--  sum |---------|
--
--  remainder = sum
--  carry = 0
--
--  ℕ   0   o       d   o       d
--------|---|-------|---|-------|
--  sum |-------------|
--
--  remainder = sum - o
--  carry = o
--
--  ℕ   0   o       d   o       d
--------|---|-------|---|-------|
--  sum |-----------------|
--
--  remainder = d + o
--  carry = sum - d + o

data Range : (d o : ℕ) (n x : Digit (suc d)) → Set where
    Before : ∀ d o {n} {x}
        → (upper-bound : sum o n x ≤ d + o)
        → Range d o n x
    Between : ∀ d o {n} {x}
        → (lower-bound : sum o n x     ≥ d + o)
        → (upper-bound : sum o n x ∸ o ≤ d + o)
        → Range d o n x
    After  : ∀ d o {n} {x}
        → (lower-bound : sum o n x ∸ o       ≥ d + o)
        → (upper-bound : sum o n x ∸ (d + o) ≤ d + o)
        → Range d o n x

range : ∀ d o n x → Range d o n x
range d o n x with sum o n x ≤? d + o
range d o n x | yes p = Before d o p
range d o n x | no ¬p with sum o n x ≤? d + o + o
range d o n x | no ¬p | yes q = Between d o lower-bound upper-bound
    where
        lower-bound : sum o n x     ≥ d + o
        lower-bound = <⇒≤ (≰⇒> ¬p)
        upper-bound : sum o n x ∸ o ≤ d + o
        upper-bound = +n-mono-inverse o $
            start
                sum o n x ∸ o + o
            ≈⟨ m∸n+n≡m (sum≥o o n x) ⟩
                sum o n x
            ≤⟨ q ⟩
                d + o + o
            □
range d o n x | no ¬p | no ¬q = After d o lower-bound upper-bound
    where
        lower-bound : sum o n x ∸ o       ≥ d + o
        lower-bound = +n-mono-inverse o $
            start
                d + o + o
            ≤⟨ <⇒≤ (≰⇒> ¬q) ⟩
                sum o n x
            ≈⟨ sym (m∸n+n≡m (sum≥o o n x)) ⟩
                sum o n x ∸ o + o
            □
        upper-bound : sum o n x ∸ (d + o) ≤ d + o
        upper-bound = +n-mono-inverse (d + o) $
            start
                sum o n x ∸ (d + o) + (d + o)
            ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
                sum o n x
            ≤⟨ sum-upper-bound o n x ⟩
                d + o + (d + o)
            □



n+-Proper-Unary : ∀ {d o}
    → (n : Digit (suc d))
    → (xs : Num 1 (suc d) o)
    → Num 1 (suc d) o
n+-Proper-Unary {d} {o} n xs with range d o n (lsd xs)
n+-Proper-Unary n (x ∙) | Before d o upper-bound
    = Digit-fromℕ (sum o n x) o upper-bound ∙
n+-Proper-Unary n (x ∷ xs) | Before d o upper-bound
    = Digit-fromℕ (sum o n x) o upper-bound ∷ xs
n+-Proper-Unary n (x ∙) | Between d o lower-bound upper-bound
    = Digit-fromℕ (sum o n x ∸ o) o upper-bound ∷ Digit-fromℕ o o (m≤n+m o d) ∙
n+-Proper-Unary n (x ∷ xs) | Between d o lower-bound upper-bound
    = Digit-fromℕ (sum o n x ∸ o) o upper-bound ∷ Digit-fromℕ o o (m≤n+m o d) ∷ xs
n+-Proper-Unary n (x ∙) | After d o lower-bound upper-bound
    = Digit-fromℕ (d + o) o ≤-refl ∷ Digit-fromℕ (sum o n x ∸ (d + o)) o upper-bound ∙
n+-Proper-Unary n (x ∷ xs) | After d o lower-bound upper-bound
    = Digit-fromℕ (d + o) o ≤-refl ∷ Digit-fromℕ (sum o n x ∸ (d + o)) o upper-bound ∷ xs

n+-Proper-Unary-toℕ : ∀ {d o}
    → (n : Digit (suc d))
    → (xs : Num 1 (suc d) o)
    → ⟦ n+-Proper-Unary n xs ⟧ ≡ Digit-toℕ n o + ⟦ xs ⟧
n+-Proper-Unary-toℕ {d} {o} n xs with range d o n (lsd xs)
n+-Proper-Unary-toℕ n (x ∙) | Before d o upper-bound =
    begin
        Digit-toℕ (Digit-fromℕ (sum o n x) o upper-bound) o
    ≡⟨ Digit-toℕ-fromℕ {d} {o} (sum o n x) upper-bound (sum≥o o n x) ⟩
        Digit-toℕ n o + Digit-toℕ x o
    ∎
n+-Proper-Unary-toℕ n (x ∷ xs) | Before d o upper-bound =
    begin
        Digit-toℕ (Digit-fromℕ (sum o n x) o upper-bound) o + ⟦ xs ⟧ * 1
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * 1) (Digit-toℕ-fromℕ {d} {o} (sum o n x) upper-bound (sum≥o o n x)) ⟩
        Digit-toℕ n o + Digit-toℕ x o + ⟦ xs ⟧ * 1
    ≡⟨ +-assoc (Digit-toℕ n o) (Digit-toℕ x o) (⟦ xs ⟧ * 1) ⟩
        Digit-toℕ n o + (Digit-toℕ x o + ⟦ xs ⟧ * 1)
    ∎
n+-Proper-Unary-toℕ n (x ∙) | Between d o lower-bound upper-bound =
    -- = Digit-fromℕ (sum o n x ∸ o) o upper-bound ∷ Digit-fromℕ o o (m≤n+m o d) ∙
    begin
        Digit-toℕ (Digit-fromℕ (sum o n x ∸ o) o upper-bound) o + Digit-toℕ (Digit-fromℕ o o (m≤n+m o d)) o * 1
    ≡⟨ cong₂ (λ w v → w + v * 1) (Digit-toℕ-fromℕ {d} {o} (sum o n x ∸ o) upper-bound {!   !}) (Digit-toℕ-fromℕ {d} {o} o (m≤n+m o d) ≤-refl) ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ∎
n+-Proper-Unary-toℕ n (x ∷ xs) | Between d o lower-bound upper-bound = {!   !}
n+-Proper-Unary-toℕ n xs | After d o lower-bound upper-bound = {!   !}

-- n+-Proper : ∀ {b d o}
--     → (cont : True (Continuous? (suc b) (suc d) o))
--     → (n : Digit (suc d))
--     → (xs : Num (suc b) (suc d) o)
--     → (proper : suc d + o ≥ 2)
--     → Num (suc b) (suc d) o
-- n+-Proper {b}     {d} {o} cont n xs proper with sum o n (lsd xs) ≤? d + o
-- n+-Proper {b}     {d} {o} cont n (x ∙)    proper | yes p = Digit-fromℕ (sum o n x) o p ∙
-- n+-Proper {b}     {d} {o} cont n (x ∷ xs) proper | yes p = Digit-fromℕ (sum o n x) o p ∷ xs
-- n+-Proper {zero}  {d} {o} cont n (x ∙)    proper | no ¬p
--     = {!   !}
--     where
--         upper-bound : (sum o n x ∸ d + o) ⊔ o ≤ d + o
--         upper-bound =
--             start
--                 (Fin.toℕ n + o + (Fin.toℕ x + o) ∸ d + o) ⊔ o
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 d + o
--             □
--         remainder : Digit (suc d)
--         remainder = Digit-fromℕ {!d + o ⊓ o   !} {!   !} {!   !}
--         carry : Digit (suc d)
--         carry = Digit-fromℕ ((sum o n x ∸ d + o) ⊔ o) o upper-bound
--     -- = Digit-fromℕ d o (m≤m+n d o) ∷ carry ∙
--     -- -- = Digit-fromℕ (d + o) o ≤-refl ∷ carry ∙
--     -- where
--     --     upper-bound : sum o n x ∸ d ≤ d + o
--     --     upper-bound =
--     --         start
--     --             Fin.toℕ n + o + (Fin.toℕ x + o) ∸ d
--     --         ≤⟨ {!   !} ⟩
--     --             {!   !}
--     --         ≤⟨ {!   !} ⟩
--     --             {!   !}
--     --         ≤⟨ {!   !} ⟩
--     --             {!   !}
--     --         ≤⟨ {!   !} ⟩
--     --             d + o
--     --         □
--     --     -- upper-bound = +n-mono-inverse (d + o) $
--     --     --     start
--     --     --         sum o n x ∸ (d + o) + (d + o)
--     --     --     ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
--     --     --         sum o n x
--     --     --     ≤⟨ sum-upper-bound o n x ⟩
--     --     --         d + o + (d + o)
--     --     --     □
--     --     carry : Digit (suc d)
--     --     carry = Digit-fromℕ (sum o n x ∸ d) o upper-bound
-- n+-Proper {zero}  {d} {o} cont n (x ∷ xs) proper | no ¬p
--     = {!   !}
--     -- = Digit-fromℕ (d + o) o ≤-refl ∷ n+-Proper cont carry xs proper
--     -- where
--     --     upper-bound : sum o n x ∸ (d + o) ≤ d + o
--     --     upper-bound = +n-mono-inverse (d + o) $
--     --         start
--     --             sum o n x ∸ (d + o) + (d + o)
--     --         ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
--     --             sum o n x
--     --         ≤⟨ sum-upper-bound o n x ⟩
--     --             d + o + (d + o)
--     --         □
--     --     carry : Digit (suc d)
--     --     carry = Digit-fromℕ (sum o n x ∸ (d + o)) o upper-bound
-- n+-Proper {suc b} {d} {o} cont n xs       proper | no ¬p with _divMod_ (sum o n (lsd xs)) (suc (suc b))
-- n+-Proper {suc b} {d} {o} cont n (x ∙)    proper | no ¬p | result quotient remainder property _ _
--     = inject≤ remainder b≤d ∷ Digit-fromℕ quotient o upper-bound ∙
--     where
--         b≤d : suc (suc b) ≤ suc d
--         b≤d =
--             start
--                 suc (suc b)
--             ≈⟨ sym (+-right-identity (suc (suc b))) ⟩
--                 1 * suc (suc b)
--             ≤⟨ *n-mono (suc (suc b)) (m≤m⊔n 1 o) ⟩
--                 (1 ⊔ o) * suc (suc b)
--             ≤⟨ ≤-pred (≰⇒> (Continuous⇒¬Gapped#0 cont proper)) ⟩
--                 suc d
--             □
--         upper-bound : quotient ≤ d + o
--         upper-bound = *n-mono-inverse (suc b)
--                      $ n+-mono-inverse (Fin.toℕ remainder)
--                      $ start
--                         Fin.toℕ remainder + quotient * suc (suc b)
--                     ≈⟨ sym property ⟩
--                         sum o n x
--                     ≤⟨ sum-upper-bound o n x ⟩
--                         (d + o) + (d + o)
--                     ≈⟨ double (d + o) ⟩
--                         (d + o) * suc (suc zero)
--                     ≤⟨ n*-mono (d + o) (s≤s (s≤s z≤n)) ⟩
--                         (d + o) * suc (suc b)
--                     ≤⟨ m≤n+m ((d + o) * suc (suc b)) (Fin.toℕ remainder) ⟩
--                         Fin.toℕ remainder + (d + o) * suc (suc b)
--                     □
-- n+-Proper {suc b} {d} {o} cont n (x ∷ xs) proper | no ¬p | result quotient remainder property _ _
--     = inject≤ remainder b≤d ∷ n+-Proper cont (Digit-fromℕ quotient o upper-bound) xs proper
--     where
--         b≤d : suc (suc b) ≤ suc d
--         b≤d =
--             start
--                 suc (suc b)
--             ≈⟨ sym (+-right-identity (suc (suc b))) ⟩
--                 1 * suc (suc b)
--             ≤⟨ *n-mono (suc (suc b)) (m≤m⊔n 1 o) ⟩
--                 (1 ⊔ o) * suc (suc b)
--             ≤⟨ ≤-pred (≰⇒> (Continuous⇒¬Gapped#0 cont proper)) ⟩
--                 suc d
--             □
--         upper-bound : quotient ≤ d + o
--         upper-bound = *n-mono-inverse (suc b)
--                      $ n+-mono-inverse (Fin.toℕ remainder)
--                      $ start
--                         Fin.toℕ remainder + quotient * suc (suc b)
--                     ≈⟨ sym property ⟩
--                         sum o n x
--                     ≤⟨ sum-upper-bound o n x ⟩
--                         (d + o) + (d + o)
--                     ≈⟨ double (d + o) ⟩
--                         (d + o) * suc (suc zero)
--                     ≤⟨ n*-mono (d + o) (s≤s (s≤s z≤n)) ⟩
--                         (d + o) * suc (suc b)
--                     ≤⟨ m≤n+m ((d + o) * suc (suc b)) (Fin.toℕ remainder) ⟩
--                         Fin.toℕ remainder + (d + o) * suc (suc b)
--                     □
--
-- n+-Proper-toℕ : ∀ {b d o}
--     → (cont : True (Continuous? (suc b) (suc d) o))
--     → (n : Digit (suc d))
--     → (xs : Num (suc b) (suc d) o)
--     → (proper : suc d + o ≥ 2)
--     → ⟦ n+-Proper cont n xs proper ⟧ ≡ Digit-toℕ n o + ⟦ xs ⟧
-- n+-Proper-toℕ {b}     {d} {o} cont n xs       proper with sum o n (lsd xs) ≤? d + o
-- n+-Proper-toℕ {b}     {d} {o} cont n (x ∙)    proper | yes p =
--     begin
--         Digit-toℕ (Digit-fromℕ (sum o n x) o p) o
--     ≡⟨ Digit-toℕ-fromℕ {d} {o} (sum o n x) upper-bound lower-bound ⟩
--         Digit-toℕ n o + Digit-toℕ x o
--     ∎
--     where
--         upper-bound : sum o n x ≤ d + o
--         upper-bound = p
--         lower-bound : sum o n x ≥ o
--         lower-bound =
--             start
--                 o
--             ≤⟨ m≤n+m o (Fin.toℕ n) ⟩
--                 Digit-toℕ n o
--             ≤⟨ m≤m+n (Digit-toℕ n o) (Digit-toℕ x o) ⟩
--                 sum o n x
--             □
-- n+-Proper-toℕ {b}     {d} {o} cont n (x ∷ xs) proper | yes p =
--     begin
--         Digit-toℕ (Digit-fromℕ (sum o n x) o p) o + ⟦ xs ⟧ * suc b
--     ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) (Digit-toℕ-fromℕ {d} {o} (sum o n x) upper-bound lower-bound) ⟩
--         Digit-toℕ n o + (Fin.toℕ x + o) + ⟦ xs ⟧ * suc b
--     ≡⟨ +-assoc (Digit-toℕ n o) (Fin.toℕ x + o) (⟦ xs ⟧ * suc b) ⟩
--         Digit-toℕ n o + (Digit-toℕ x o + ⟦ xs ⟧ * suc b)
--     ∎
--     where
--         upper-bound : sum o n x ≤ d + o
--         upper-bound = p
--         lower-bound : sum o n x ≥ o
--         lower-bound =
--             start
--                 o
--             ≤⟨ m≤n+m o (Fin.toℕ n) ⟩
--                 Digit-toℕ n o
--             ≤⟨ m≤m+n (Digit-toℕ n o) (Digit-toℕ x o) ⟩
--                 sum o n x
--             □
-- -- n+-Proper {zero}  {d} {o} cont n (x ∷ xs) proper | no ¬p
-- --     = Digit-fromℕ (d + o) o ≤-refl ∷ n+-Proper cont carry xs proper
-- --     where
-- --         upper-bound : sum o n x ∸ (d + o) ≤ d + o
-- --         upper-bound = +n-mono-inverse (d + o) $
-- --             start
-- --                 sum o n x ∸ (d + o) + (d + o)
-- --             ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
-- --                 sum o n x
-- --             ≤⟨ sum-upper-bound o n x ⟩
-- --                 d + o + (d + o)
-- --             □
-- --         carry : Digit (suc d)
-- --         carry = Digit-fromℕ (sum o n x ∸ (d + o)) o upper-bound
--
--
-- n+-Proper-toℕ {zero}  {d} {o} cont n (x ∙) proper | no ¬p =
--     {!   !}
    -- begin
    --     Digit-toℕ (Digit-fromℕ (d + o) o ≤-refl) o + Digit-toℕ carry o * 1
    -- ≡⟨ cong (λ w → w + Digit-toℕ carry o * 1) (Digit-toℕ-fromℕ {d} {o} (d + o) ≤-refl (m≤n+m o d))  ⟩
    --     d + o + Digit-toℕ carry o * 1
    -- ≡⟨ cong (λ w → d + o + w) $
    --     begin
    --         Digit-toℕ carry o * 1
    --     ≡⟨ *-right-identity (Digit-toℕ carry o) ⟩
    --         Digit-toℕ carry o
    --     ≡⟨ Digit-toℕ-fromℕ {d} {o} (sum o n x ∸ (d + o)) upper-bound lower-bound ⟩
    --         sum o n x ∸ (d + o)
    --     ∎
    -- ⟩
    --     d + o + (sum o n x ∸ (d + o))
    -- ≡⟨ +-comm (d + o) (sum o n x ∸ (d + o)) ⟩
    --     sum o n x ∸ (d + o) + (d + o)
    -- ≡⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
    --     sum o n x
    -- ∎
    -- where
    --     upper-bound : sum o n x ∸ (d + o) ≤ d + o
    --     upper-bound = +n-mono-inverse (d + o) $
    --         start
    --             sum o n x ∸ (d + o) + (d + o)
    --         ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬p)) ⟩
    --             sum o n x
    --         ≤⟨ sum-upper-bound o n x ⟩
    --             d + o + (d + o)
    --         □
    --     lower-bound : sum o n x ∸ (d + o) ≥ o
    --     lower-bound = sum-lower-bound' o n x (≰⇒> ¬p) (≤-pred (≰⇒> (Continuous⇒¬Gapped#0 cont proper)))
    --
    --     carry : Digit (suc d)
    --     carry = Digit-fromℕ (sum o n x ∸ (d + o)) o upper-bound
-- n+-Proper-toℕ {zero}  {d} {o} cont n (x ∷ xs) proper | no ¬p = {!   !}
-- n+-Proper-toℕ {suc b} {d} {o} cont n xs proper | no ¬p = {!   !}

-- n+ : ∀ {b d o}
--     → {cont : True (Continuous? b d o)}
--     → ℕ
--     → (xs : Num b d o)
--     → Num b d o
-- n+ {b} {d} {o} {cont} n xs with numView b d o
-- n+ {_} {_} {_} {()}   n xs | NullBase d o
-- n+ {_} {_} {_} {cont} n xs | NoDigits b o = NoDigits-explode xs
-- n+ {_} {_} {_} {()}   n xs | AllZeros b
-- n+ n (x ∙) | Proper b d o proper with _divMod_ (n + Fin.toℕ x + o) (suc b)
-- n+ n (x ∙) | Proper b d o proper | result zero remainder property div-eq mod-eq
--     = inject≤ remainder b≤d ∙
--     where
--         b≤d : suc b ≤ suc d
--         b≤d =
--             start
--                 suc b
--             ≈⟨ sym (+-right-identity (suc b)) ⟩
--                 1 * suc b
--             ≤⟨ *n-mono (suc b) (m≤m⊔n 1 o) ⟩
--                 (1 ⊔ o) * suc b
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 suc d
--             □
-- n+ n (x ∙) | Proper b d o proper | result (suc quotient) remainder property div-eq mod-eq
--     = inject≤ remainder b≤d ∷ {!   !}
--     where
--         b≤d : suc b ≤ suc d
--         b≤d = {!   !}
-- n+ n (x ∷ xs) | Proper b d o proper with _divMod_ (n + Fin.toℕ x + o) (suc b)
-- n+ {cont = cont} n (x ∷ xs) | Proper b d o proper | result quotient remainder property div-eq mod-eq
--     = inject≤ remainder b≤d ∷ n+ {cont = {! cont  !}} quotient xs
--     where
--         b≤d : suc b ≤ suc d
--         b≤d = {!   !}

-- n+ : ∀ {b d o}
--     → {cont : True (Continuous? b d o)}
--     → (x : Digit d)
--     → (ys : Num b d o)
--     → Num b d o
-- n+ {b} {d} {o} {cont} x ys with numView b d o
-- n+ {_} {_} {_} {()}   x ys | NullBase d o
-- n+ {_} {_} {_} {cont} x ys | NoDigits b o = NoDigits-explode ys
-- n+ {_} {_} {_} {()}   x ys | AllZeros b
-- n+ x (y ∙) | Proper b d o proper with _divMod_ (Fin.toℕ x + Fin.toℕ y + o) (suc b)
-- n+ x (y ∙) | Proper b d o proper | result zero remainder property div-eq mod-eq
--     = inject≤ remainder b≤d ∙
--     where
--         b≤d : suc b ≤ suc d
--         b≤d =
--             start
--                 suc b
--             ≈⟨ sym (+-right-identity (suc b)) ⟩
--                 1 * suc b
--             ≤⟨ *n-mono (suc b) (m≤m⊔n 1 o) ⟩
--                 (1 ⊔ o) * suc b
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 {!   !}
--             ≤⟨ {!   !} ⟩
--                 suc d
--             □
-- n+ x (y ∙) | Proper b d o proper | result (suc quotient) remainder property div-eq mod-eq
--     = inject≤ remainder b≤d ∷ n+ {! quotient  !} {!   !}
--     where
--         b≤d : suc b ≤ suc d
--         b≤d = {!   !}
-- n+ x (y ∷ ys) | Proper b d o proper = {!   !}
-- n+ x ys | Proper b d o proper with nextView ys proper
-- n+ x ys | Proper b d o proper | NeedNoCarry _ _ _ ¬greatest = {!   !}
-- n+ x (ys ∙) | Proper b d o proper | IsGapped _ _ _ greatest gapped = {!   !}
-- n+ x (y ∷ ys) | Proper b d o proper | IsGapped _ _ _ greatest gapped = {! ys  !}
-- n+ x ys | Proper b d o proper | NotGapped _ _ _ greatest ¬gapped = {!   !}

-- n+ x (y ∙) | Proper b d o proper with Digit-toℕ x o + Digit-toℕ y o ≤? suc d + o
-- n+ x (y ∙) | Proper b d o proper | yes carry = {!   !}
-- n+ x (y ∙) | Proper b d o proper | no ¬carry = {!   !}
-- n+ x (y ∷ ys) | Proper b d o proper = {!   !}


-- n+ {b} {d} {o}
-- n+ x (x' ∙) = {!   !}
-- n+ x (x' ∷ xs) = {!   !}

-- -- a partial function that only maps ℕ to Continuous Nums
fromℕ : ∀ {b d o}
    → {cont : True (Continuous? b (suc d) o)}
    → ℕ
    → Num b (suc d) o
fromℕ {cont = cont} zero = z ∙
fromℕ {cont = cont} (suc n) = 1+ {cont = cont} (fromℕ {cont = cont} n)

toℕ-fromℕ : ∀ {b d o}
    → {cont : True (Continuous? b (suc d) o)}
    → (n : ℕ)
    → ⟦ fromℕ {cont = cont} n ⟧ ≡ n + o
toℕ-fromℕ {_} {_} {_} {cont} zero = refl
toℕ-fromℕ {b} {d} {o} {cont} (suc n) =
    begin
        ⟦ 1+ {cont = cont} (fromℕ {cont = cont} n) ⟧
    ≡⟨ 1+-toℕ {cont = cont} (fromℕ {cont = cont} n) ⟩
        suc ⟦ fromℕ {cont = cont} n ⟧
    ≡⟨ cong suc (toℕ-fromℕ {cont = cont} n) ⟩
        suc (n + o)
    ∎

-- Num 10 1000 100
--
-- Digits : { 100 ~ 1099 }

-- 1099 + 1099 ≡  + 1098 . 110
-- 1099

-- 100 100

-- (x + y + 2o) / b ≡ 20

-- 2198 - 100 = 2098 ÷ 10 = 209 ... 8
--
-- 108 + 2090 =

-- _⊹_ : ∀ {b d o}
--     → {cont : True (Continuous? b d o)}
--     → (xs ys : Num b d o)
--     → Num b d o
-- -- _⊹_ {b} {d} {o} {cont} (x ∙)    (y ∙)    = {!   !}
-- _⊹_ {b} {d} {o} {cont} (x ∙)    (y ∙)    with _divMod_ (Fin.toℕ x + Fin.toℕ y + o) b {{!   !}}
-- _⊹_ {b} {d} {o} {cont} (x ∙)    (y ∙)    | result quotient remainder property div-eq mod-eq
--     = inject≤ remainder d≥b ∷ {!   !}
--     where   d≥b : d ≥ b
--             d≥b = ≤-pred $
--                 start
--                     suc b
--                 ≈⟨ sym (+-right-identity (suc b)) ⟩
--                     1 * suc b
--                 ≤⟨ *n-mono (suc b) (m≤m⊔n 1 o) ⟩
--                     (1 ⊔ o) * suc b
--                 ≤⟨ {!   !} ⟩
--                     {!   !}
--                 ≤⟨ {!   !} ⟩
--                     {!   !}
--                 ≤⟨ {!   !} ⟩
--                     suc d
--                 □
--     -- = {!   !}
-- _⊹_ {b} {d} {o} {cont} (x ∙)    (y ∷ ys) = {!   !}
-- _⊹_ {b} {d} {o} {cont} (x ∷ xs) (y ∙)    = {!   !}
-- _⊹_ {b} {d} {o} {cont} (x ∷ xs) (y ∷ ys) = {!   !}
-- (x ∙)    ⊹ (y ∙) = {!   !}
-- (x ∙)    ⊹ (y ∷ ys) = {!   !}
-- (x ∷ xs) ⊹ (y ∙) = {!   !}
-- (x ∷ xs) ⊹ (y ∷ ys) = {!   !}

module Example where

    three : Num 2 2 0
    three = s z ∷ s z ∙


--
-- _⊹_ : ∀ {b d o}
--     → {surj : True (Surjective? b d o)}
--     → (xs ys : Num b d o)
--     → Num b d o
-- _⊹_ {b} {d} {o}      xs       ys        with Surjective? b d o
-- _⊹_ {b} {d} {o}      ∙        ∙        | yes surj = ∙
-- _⊹_ {b} {d} {o}      ∙        (y ∷ ys) | yes surj = y ∷ ys
-- _⊹_ {b} {d} {o}      (x ∷ xs) ∙        | yes surj = x ∷ xs
-- _⊹_ {b} {d} {o}      (x ∷ xs) (y ∷ ys) | yes surj with _divMod_ (o + Fin.toℕ x + Fin.toℕ y) b {fromWitnessFalse (>⇒≢ (Surjective⇒b≥1 surj))}
-- _⊹_ {b} {d} {o}      (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq =
--     inject≤ remainder d≥b ∷ n+ quotient (_⊹_ {surj = fromWitness surj} xs ys)
--     where   d≥b : d ≥ b
--             d≥b = Surjective⇒d≥b surj
-- _⊹_ {b} {d} {o} {()} xs ys | no ¬surj
--
--
-- -- (incrementable n) if there exists some n' : Num b d o such that ⟦ n' ⟧ℕ ≡ suc ⟦ n ⟧ℕ
-- incrementable : ∀ {b d o} → Num b d o → Set
-- incrementable {b} {d} {o} xs = Σ[ xs' ∈ Num b d o ] toℕ xs' ≡ suc (toℕ xs)
--
-- -- when a system has no digits at all
-- incrementable-lemma-no-digits : ∀ {b o} → (xs : Num b 0 o) → ¬ (incrementable xs)
-- incrementable-lemma-no-digits ∙ (∙ , ())
-- incrementable-lemma-no-digits ∙ (() ∷ xs , p)
-- incrementable-lemma-no-digits (() ∷ xs)
--
-- Num-b-1-0⇒≡0 : ∀ {b} → (xs : Num b 1 0) → toℕ xs ≡ 0
-- Num-b-1-0⇒≡0     ∙           = refl
-- Num-b-1-0⇒≡0 {b} (z    ∷ xs) = cong (λ w → w * b) (Num-b-1-0⇒≡0 xs)
-- Num-b-1-0⇒≡0     (s () ∷ xs)
--
-- Num-0-d-o⇒<d+o : ∀ {d o} → (xs : Num 0 (suc d) o) → toℕ xs < suc d + o
-- Num-0-d-o⇒<d+o ∙ = s≤s z≤n
-- Num-0-d-o⇒<d+o {d} {o} (x ∷ xs) = s≤s $
--     start
--         Digit-toℕ x o + toℕ xs * zero
--     ≤⟨ reflexive $ begin
--             Digit-toℕ x o + toℕ xs * zero
--         ≡⟨ cong (_+_ (Digit-toℕ x o)) (*-right-zero (toℕ xs)) ⟩
--             Digit-toℕ x o + zero
--         ≡⟨ +-right-identity (Digit-toℕ x o) ⟩
--             Digit-toℕ x o
--     ∎ ⟩
--         Digit-toℕ x o
--     ≤⟨ ≤-pred (Digit<d+o x o) ⟩
--         d + o
--     □
--
-- -- when a system has only the digit 0
-- Num-b-1-0⇒¬incrementable : ∀ {b} → (xs : Num b 1 0) → ¬ (incrementable xs)
-- Num-b-1-0⇒¬incrementable {b} xs (xs' , p) = contradiction (
--     begin
--         0
--     ≡⟨ sym (Num-b-1-0⇒≡0 xs') ⟩
--         toℕ xs'
--     ≡⟨ p ⟩
--         suc (toℕ xs)
--     ≡⟨ cong suc (Num-b-1-0⇒≡0 xs) ⟩
--         1
--     ∎) (λ ())
--
-- incrementable-lemma-2 : ∀ {b d o} → ¬ (incrementable {b} {suc d} {suc (suc o)} ∙)
-- incrementable-lemma-2 (∙ , ())
-- incrementable-lemma-2 (x ∷ xs , ())
--
-- incrementable-lemma-3 : ∀ {d o}
--     → (x : Digit (suc d)) → (xs : Num 0 (suc d) o)
--     → suc (Fin.toℕ x) ≡ suc d
--     → ¬ (incrementable (x ∷ xs))
-- incrementable-lemma-3 x xs p (∙ , ())
-- incrementable-lemma-3 {d} {o} x xs p (x' ∷ xs' , q) =
--     let x'≡1+x : Fin.toℕ x' ≡ suc (Fin.toℕ x)
--         x'≡1+x  = cancel-+-left o
--                 $ cancel-+-right 0
--                 $ begin
--                     o + Fin.toℕ x' + zero
--                 ≡⟨ cong (_+_ (Digit-toℕ x' o)) (sym (*-right-zero (toℕ xs'))) ⟩
--                     Digit-toℕ x' o + toℕ xs' * zero
--                 ≡⟨ q ⟩
--                     suc (Digit-toℕ x o + toℕ xs * zero)
--                 ≡⟨ cong (_+_ (suc (Digit-toℕ x o))) (*-right-zero (toℕ xs)) ⟩
--                     suc (o + Fin.toℕ x + zero)
--                 ≡⟨ cong (λ w → w + zero) (sym (+-suc o (Fin.toℕ x))) ⟩
--                     o + suc (Fin.toℕ x) + zero
--                 ∎
--         x'≡1+d : Fin.toℕ x' ≡ suc d
--         x'≡1+d =
--             begin
--                 Fin.toℕ x'
--             ≡⟨ x'≡1+x ⟩
--                 suc (Fin.toℕ x)
--             ≡⟨ p ⟩
--                 suc d
--             ∎
--         x'≢1+d : Fin.toℕ x' ≢ suc d
--         x'≢1+d = <⇒≢ (bounded x')
--     in contradiction x'≡1+d x'≢1+d
--
-- incrementable-lemma-4 : ∀ {b d o}
--     → (x : Digit (suc d))
--     → (xs xs' : Num (suc b) (suc d) o)
--     → toℕ xs' ≡ suc (toℕ xs)
--     → (isFull : suc (Fin.toℕ x) ≡ suc d)
--     → toℕ (digit+1-b {suc b} x (s≤s z≤n) isFull ∷ xs') ≡ suc (toℕ (x ∷ xs))
-- incrementable-lemma-4 x xs xs' p full = {!   !}
--
--
--
-- -- begin
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ∎
--
-- incrementable? : ∀ {b d o} → (xs : Num b d o) → Dec (incrementable xs)
-- -- no digits at all
-- incrementable? {_} {zero}               xs = no (incrementable-lemma-no-digits xs)
-- -- all numbers evaluates to 0
-- incrementable? {_} {suc zero}    {zero} ∙  = no (Num-b-1-0⇒¬incrementable ∙)
-- incrementable? {_} {suc (suc d)} {zero} ∙  = yes ((fromℕ≤ {1} (s≤s (s≤s z≤n)) ∷ ∙) , refl)
-- incrementable? {d = suc d} {suc zero} ∙ = yes (z ∷ ∙ , refl)
-- -- digits starts from 2, impossible to increment from 0
-- incrementable? {d = suc d} {suc (suc o)} ∙ = no incrementable-lemma-2
-- -- see if the LSD is at its largest
-- incrementable? {d = suc d} (x ∷ xs) with full x
-- -- the system is bounded because base = 0
-- incrementable? {zero} {suc d} (x ∷ xs) | yes p = no (incrementable-lemma-3 x xs p)
-- incrementable? {suc b} {suc d} (x ∷ xs) | yes p with incrementable? xs
-- incrementable? {suc b} {suc d} (x ∷ xs) | yes p | yes (xs' , q) with b ≤? d
-- incrementable? {suc b} {suc d} (x ∷ xs) | yes p | yes (xs' , q) | yes r
--     = yes (digit+1-b {suc b} x (s≤s z≤n) p ∷ xs' , {!   !})
-- incrementable? {suc b} {suc d} (x ∷ xs) | yes p | yes (xs' , q) | no ¬r = no {!   !}
-- incrementable? {suc b} {suc d} (x ∷ xs) | yes p | no ¬q = no {!   !}
-- incrementable? {b} {suc d} (x ∷ xs) | no ¬p = yes {!   !}
--
-- mutual
--
--     1+ : ∀ {b d o} → (xs : Num b d o) → True (incrementable? xs) → Num b d o
--     1+ {d = zero} xs ()
--     1+ {d = suc zero} {zero} ∙ ()
--     1+ {d = suc (suc d)} {zero} ∙ p = fromℕ≤ {1} (s≤s (s≤s z≤n)) ∷ ∙
--     1+ {d = suc d} {suc zero} ∙ p = z ∷ ∙
--     1+ {d = suc d} {suc (suc o)} ∙ p = contradiction (toWitness p) ((incrementable-lemma-2 {_} {d} {o}))
--     1+ {d = suc d} (x ∷ xs) incr with full x
--     1+ {b} {suc d} (x ∷ xs) incr | yes p with incrementable? xs
--     1+ {b} {suc d} (x ∷ xs) incr | yes p | yes q with b ≤? d
--     1+ {b} {suc d} (x ∷ xs) incr | yes p | yes q | yes r = {!   !}
--     1+ {b} {suc d} (x ∷ xs) incr | yes p | yes q | no ¬r = {!   !}
--     1+ {b} {suc d} (x ∷ xs) incr | yes p | no ¬q = {!   !}
--     1+ {b} {suc d} (x ∷ xs) incr | no ¬p = {!   !}
--
-- -- -- no digits
-- -- incrementable? {b} {zero} {o} ∙ = no (incrementable-lemma-no-digits ∙)
-- -- -- the system only the digit 0
-- -- incrementable? {b} {suc zero} {zero} ∙ = no (Num-b-1-0⇒¬incrementable ∙)
-- -- -- the system has 2 digits {0, 1}
-- -- incrementable? {b} {suc (suc d)} {zero} ∙ = yes ((fromℕ≤ {1} (s≤s (s≤s z≤n)) ∷ ∙) , refl)
-- -- incrementable? {b} {suc d} {suc zero} ∙ = yes (z ∷ ∙ , refl)
-- -- -- offset = 2, it's impossible for "1" to exist
-- -- incrementable? {b} {suc d} {suc (suc o)} ∙ = no incrementable-lemma-2
-- -- incrementable? {b} {d} {o} (x ∷ xs) with full x
-- -- -- x is at its largest, needs to carry in order to be incrementable
-- -- incrementable? (x ∷ xs) | yes p with incrementable? xs
-- -- incrementable? (x ∷ xs) | yes p | yes q = yes ((fromℕ≤ {0} {!   !} ∷ {!   !}) , {!   !})
-- -- incrementable? (x ∷ xs) | yes p | no ¬q = {!   !}
-- -- incrementable? (x ∷ xs) | no ¬p = yes ((digit+1 x ¬p ∷ xs) , {!   !})
--
-- -- incrementable? : ∀ {b d o} → (xs : Num b d o) → Dec (incrementable xs)
-- -- incrementable? ∙ = {!   !}
-- -- incrementable? (x ∷ xs) = {!   !}
-- -- incrementable? : ∀ {b d o}
-- --     → (xs : Num b d o)
-- --     →
-- --     → Σ[ xs' ∈ Num b d o ] toℕ xs' ≡ suc (toℕ xs)
-- -- incrementable? ∙ = {!   !} , {!   !}
-- -- incrementable? (x ∷ xs) = {!   !}
--
--
--
-- normalize : ∀ {b d o} → Num b d o → Num b d o
-- normalize {b} {d} {o} ∙ = ∙
-- normalize {b} {d} {o} (x ∷ xs) with Injective? b d o
-- -- injective systems are not redundant, normalization has no effects on these numbers
-- normalize {b} {d} {o} (x ∷ xs) | yes inj = x ∷ xs
-- normalize {b} {d} {o} (x ∷ xs) | no ¬inj with Surjective? b d o
-- normalize {b} {d} {o} (x ∷ xs) | no ¬inj | yes surj with _divMod_ (Digit-toℕ x o) b {fromWitnessFalse (>⇒≢ (Surjective⇒b≥1 surj))}
-- normalize {b} {d} {o} (x ∷ xs) | no ¬inj | yes surj | result quotient remainder property div-eq mod-eq
--     = LSD ∷ n+ quotient xs
--     where   d≥b : d ≥ b
--             d≥b = Surjective⇒d≥b surj
--             LSD : Digit d
--             LSD = inject≤ remainder d≥b
-- normalize (x ∷ ∙) | no ¬inj | no ¬surj = {!   !}
-- normalize (x ∷ y ∷ xs) | no ¬inj | no ¬surj = {!   !}
--
-- -- normalize : ∀ {b d o} → Num b d o → Num b d o
-- -- normalize {b} {d} {o} ∙ = ∙
-- -- normalize {b} {d} {o} (x ∷ xs) with injectionView b d o
-- -- -- injective systems are not redundant, normalization has no effects on these numbers
-- -- normalize {b} {d} {o} (x ∷ xs) | Inj _ = xs
-- --
-- -- normalize {b} {d} {o} (x ∷ xs) | NonInj _ with surjectionView b d o
-- -- normalize {b} {d} {o} (x ∷ xs) | NonInj _ | Surj surjCond with (Digit-toℕ x o) divMod b
-- -- normalize {b} {d} {o} (x ∷ xs) | NonInj _ | Surj surjCond | result quotient remainder property div-eq mod-eq
-- --     = {!   !} ∷ {!   !}
-- --     where   d≥b : d ≥ b
-- --             d≥b = Surjective⇒d≥b surj
-- -- normalize {b} {d} {o} (x ∷ xs) | NonInj _ | NonSurj _ = {!   !}
--
-- _≋_ : ∀ {b d o}
--     → (xs ys : Num b d o)
--     → Set
-- _≋_ {b}     {d}     {o} ∙        ∙        = ⊤
--
-- _≋_ {b}     {d}     {o} ∙        (y ∷ ys) with Digit-toℕ y o ≟ 0
-- _≋_ {zero}  {d}     {o} ∙        (y ∷ ys) | yes p = ⊤
-- _≋_ {suc b} {d}         ∙        (y ∷ ys) | yes p = ∙ ≋ ys
-- _≋_ {b}     {d}         ∙        (y ∷ ys) | no ¬p = ⊥
--
-- _≋_ {b}     {d}     {o} (x ∷ xs) ∙        with Digit-toℕ x o ≟ 0
-- _≋_ {zero}              (x ∷ xs) ∙        | yes p = ⊤
-- _≋_ {suc b}             (x ∷ xs) ∙        | yes p = xs ≋ ∙
-- _≋_ {b}     {d}     {o} (x ∷ xs) ∙        | no ¬p = ⊥
-- -- things get trickier here, we cannot say two numbers are equal or not base on
-- -- their LSD, since the system may be redundant.
-- _≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) with Digit-toℕ x o ≟ Digit-toℕ y o
-- _≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) | yes p = xs ≋ ys
-- _≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) | no ¬p = ⊥
--
-- -- indexing bijective systems
-- BijN : ℕ → Set
-- BijN b = Num (suc b) (suc b) 1
--
-- BijN⇒Surjective : ∀ b → Surjective (Num⟶ℕ (suc b) (suc b) 1)
-- BijN⇒Surjective b with surjectionView (suc b) (suc b) 1
-- BijN⇒Surjective b | Surj surjCond = SurjCond⇒Surjective surjCond
-- BijN⇒Surjective b | NonSurj (Offset≥2 (s≤s ()))
-- BijN⇒Surjective b | NonSurj (NotEnoughDigits _ d≱b) = contradiction (s≤s ≤-refl) d≱b
--
-- BijN⇒Injective : ∀ b → Injective (Num⟶ℕ (suc b) (suc b) 1)
-- BijN⇒Injective b with injectionView (suc b) (suc b) 1
-- BijN⇒Injective b | Inj injCond = InjCond⇒Injective injCond
-- BijN⇒Injective b | NonInj (Redundant d>b) = contradiction refl (>⇒≢ d>b)
--
-- BijN⇒Bijective : ∀ b → Bijective (Num⟶ℕ (suc b) (suc b) 1)
-- BijN⇒Bijective b with bijectionView (suc b) (suc b) 1
-- BijN⇒Bijective b | Bij surjCond injCond = SurjCond∧InjCond⇒Bijective surjCond injCond
-- BijN⇒Bijective b | NonSurj (Offset≥2 (s≤s ()))
-- BijN⇒Bijective b | NonSurj (NotEnoughDigits _ d≱b) = contradiction (s≤s ≤-refl) d≱b
-- BijN⇒Bijective b | NonInj (Redundant d>b) = contradiction refl (>⇒≢ d>b)
