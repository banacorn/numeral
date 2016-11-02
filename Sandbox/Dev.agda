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
    → (n x : Digit (suc d))
    → sum o n x ≥ o
sum≥o o n x = start
        o
    ≤⟨ m≤n+m o (Fin.toℕ n) ⟩
        Digit-toℕ n o
    ≤⟨ m≤m+n (Digit-toℕ n o) (Digit-toℕ x o) ⟩
        sum o n x
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
        → (property : Digit-toℕ leftover o + (Digit-toℕ carry o) * suc b ≡ sum o y x)
        → Sum b d o y x

sumView : ∀ b d o
    → (¬gapped : (1 ⊔ o) * suc b ≤ suc d)
    → (proper : suc d + o ≥ 2)
    → (y : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → Sum b d o y (lsd xs)
sumView b d o ¬ proper y xs with (sum o y (lsd xs)) ≤? d + o
sumView b d o ¬ proper y xs | yes p
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
sumView b d o ¬ proper y xs | no ¬p with _divMod_ (sum o y (lsd xs) ∸ (d + o)) (suc b)
sumView b d o ¬ proper y xs | no ¬p | result quotient remainder divModProp _ _
    = Carried
        (Digit-fromℕ leftover o {!   !})
        {!   !}
        {!   !}
    where

        carry : ℕ
        carry = suc b + quotient * suc b

        carry>dividend : carry > sum o y (lsd xs) ∸ (d + o)
        carry>dividend =
            start
                suc (sum o y (lsd xs) ∸ (d + o))
            ≈⟨ cong suc divModProp ⟩
                suc (Fin.toℕ remainder + quotient * suc b)
            ≤⟨ +n-mono (quotient * suc b) (bounded remainder) ⟩
                suc b + quotient * suc b
            ≈⟨ refl ⟩
                carry
            □

        leftover : ℕ
        leftover = sum o y (lsd xs) ∸ carry

        leftover-upper-bound : leftover ≤ d + o
        leftover-upper-bound =
            start
                sum o y (lsd xs) ∸ carry
            ≤⟨ ∸-mono {sum o y (lsd xs)} {sum o y (lsd xs)} ≤-refl carry>dividend ⟩
                sum o y (lsd xs) ∸ suc (sum o y (lsd xs) ∸ (d + o))
            ≈⟨ sym (∸-+-assoc (sum o y (lsd xs)) 1 (sum o y (lsd xs) ∸ (d + o))) ⟩
                (sum o y (lsd xs) ∸ 1) ∸ (sum o y (lsd xs) ∸ (d + o))
            ≤⟨ ∸-mono {sum o y (lsd xs) ∸ 1} {sum o y (lsd xs) ∸ (d + o)} {sum o y (lsd xs) ∸ (d + o)} (∸-mono {sum o y (lsd xs)} {sum o y (lsd xs)} {1} {d + o} ≤-refl {! proper  !}) ≤-refl ⟩
                (sum o y (lsd xs) ∸ (d + o)) ∸ (sum o y (lsd xs) ∸ (d + o))
            ≤⟨ {!   !} ⟩
                {!   !}
            ≤⟨ {!   !} ⟩
                d + o
            □
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
