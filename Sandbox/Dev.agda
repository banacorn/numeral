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

        carry : ℕ
        carry = (1 ⊓ Fin.toℕ remainder) + quotient + (1 ⊔ o)

        divModProp' : sum o x y ≡ Fin.toℕ remainder + quotient * base + (d + o + (1 ⊔ o) * base)
        divModProp' =
            begin
                sum o x y
            ≡⟨ sym (m∸n+n≡m (<⇒≤ (≰⇒> ¬within))) ⟩
                sum o x y ∸ (d + o + (1 ⊔ o) * base) + (d + o + (1 ⊔ o) * base)
            ≡⟨ cong (λ w → w + ((d + o) + (1 ⊔ o) * base)) divModProp ⟩
                Fin.toℕ remainder + quotient * base + ((d + o) + (1 ⊔ o) * base)
            ∎

        leftover : ℕ
        leftover = sum o x y ∸ carry * base

        leftover-lower-bound-lemma :
              (remainder : Fin base)
            → (prop : sum o x y ∸ (d + o + (1 ⊔ o) * base) ≡ Fin.toℕ remainder + quotient * base)
            → sum o x y ≥ o + ((1 ⊓ Fin.toℕ remainder) + quotient + (1 ⊔ o)) * base
        leftover-lower-bound-lemma z prop =
            start
                o + (quotient + (1 ⊔ o)) * base
            ≤⟨ +n-mono ((quotient + (1 ⊔ o)) * base) (m≤n+m o d) ⟩
                d + o + (quotient + (1 ⊔ o)) * base
            ≈⟨ cong (λ w → d + o + w) (distribʳ-*-+ base quotient (1 ⊔ o)) ⟩
                d + o + (quotient * base + (1 ⊔ o) * base)
            ≈⟨ a+[b+c]≡b+[a+c] (d + o) (quotient * base) ((1 ⊔ o) * base) ⟩
                quotient * base + ((d + o) + (1 ⊔ o) * base)
            ≈⟨ cong (λ w → w + ((d + o) + (1 ⊔ o) * base)) (sym prop) ⟩
                (sum o x y ∸ ((d + o) + (1 ⊔ o) * base)) + ((d + o) + (1 ⊔ o) * base)
            ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬within)) ⟩
                sum o x y
            □
        leftover-lower-bound-lemma (s r) prop =
            start
                o + ((1 ⊓ (Fin.toℕ (s r))) + quotient + (1 ⊔ o)) * base
            ≈⟨ refl ⟩
                o + (1 + (quotient + (1 ⊔ o))) * base
            ≈⟨ cong (λ w → o + w) (distribʳ-*-+ base 1 (quotient + (1 ⊔ o))) ⟩
                o + (1 * base + (quotient + (1 ⊔ o)) * base)
            ≈⟨ cong (λ w → o + (1 * base + w)) (distribʳ-*-+ base quotient (1 ⊔ o)) ⟩
                o + (1 * base + (quotient * base + (1 ⊔ o) * base))
            ≤⟨ n+-mono o
                (n+-mono (1 * base)
                    (+n-mono ((1 ⊔ o) * base)
                        (m≤n+m (quotient * base) (Fin.toℕ r)))) ⟩
                o + (1 * base + (Fin.toℕ r + quotient * base + (1 ⊔ o) * base))
            ≈⟨ a+[b+c]≡b+[a+c] o (1 * base) (Fin.toℕ r + quotient * base + (1 ⊔ o) * base) ⟩
                1 * base + (o + (Fin.toℕ r + quotient * base + (1 ⊔ o) * base))
            ≤⟨ +n-mono (o + (Fin.toℕ r + quotient * base + (1 ⊔ o) * base)) (*n-mono base (m≤m⊔n 1 o)) ⟩
                (1 ⊔ o) * base + (o + (Fin.toℕ r + quotient * base + (1 ⊔ o) * base))
            ≤⟨ +n-mono (o + ((Fin.toℕ r) + quotient * base + (1 ⊔ o) * base)) ¬gapped ⟩
                suc d + (o + ((Fin.toℕ r) + quotient * base + (1 ⊔ o) * base))
            ≈⟨ cong suc (sym (+-assoc d o ((Fin.toℕ r) + quotient * base + (1 ⊔ o) * base))) ⟩
                suc (d + o + ((Fin.toℕ r) + quotient * base + (1 ⊔ o) * base))
            ≈⟨ sym (+-suc (d + o) ((Fin.toℕ r) + quotient * base + (1 ⊔ o) * base)) ⟩
                d + o + suc ((Fin.toℕ r) + quotient * base + (1 ⊔ o) * base)
            ≈⟨ a+[b+c]≡b+[a+c] (d + o) (suc (Fin.toℕ r) + quotient * base) ((1 ⊔ o) * base) ⟩
                suc (Fin.toℕ r) + quotient * base + ((d + o) + (1 ⊔ o) * base)
            ≈⟨ cong (λ w → w + ((d + o) + (1 ⊔ o) * base)) (sym prop) ⟩
                (sum o x y ∸ ((d + o) + (1 ⊔ o) * base)) + ((d + o) + (1 ⊔ o) * base)
            ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬within)) ⟩
                sum o x y
            □

        leftover-lower-bound : leftover ≥ o
        leftover-lower-bound =
            start
                o
            ≈⟨ sym (m+n∸n≡m o (carry * base)) ⟩
                o + carry * base ∸ carry * base
            ≤⟨ ∸n-mono (carry * base) (leftover-lower-bound-lemma remainder divModProp) ⟩
                sum o x y ∸ carry * base
            ≈⟨ refl ⟩
                leftover
            □

        leftover-upper-bound-lemma :
              (remainder : Fin base)
            → (prop : sum o x y ∸ (d + o + (1 ⊔ o) * base) ≡ Fin.toℕ remainder + quotient * base)
            → sum o x y ≤ d + o + ((1 ⊓ Fin.toℕ remainder) + quotient + (1 ⊔ o)) * base
        leftover-upper-bound-lemma z prop =
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
            □
        leftover-upper-bound-lemma (s r) prop =
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
            ≈⟨ refl ⟩
                d + o + ((1 ⊓ (Fin.toℕ (s r))) + quotient + (1 ⊔ o)) * base
            □

        leftover-upper-bound : leftover ≤ d + o
        leftover-upper-bound =
            start
                leftover
            ≈⟨ refl ⟩
                sum o x y ∸ carry * base
            ≤⟨ ∸n-mono (carry * base) (leftover-upper-bound-lemma remainder divModProp) ⟩
                d + o + carry * base ∸ carry * base
            ≈⟨ m+n∸n≡m (d + o) (carry * base) ⟩
                d + o
            □

        carry-lower-bound : carry ≥ o
        carry-lower-bound =
            start
                o
            ≤⟨ m≤n⊔m o 1 ⟩
                1 ⊔ o
            ≤⟨ m≤n+m (1 ⊔ o) (1 ⊓ Fin.toℕ remainder + quotient) ⟩
                1 ⊓ Fin.toℕ remainder + quotient + (1 ⊔ o)
            □

        carry-upper-bound : carry ≤ d + o
        carry-upper-bound = +n-mono-inverse (d + o) $
            start
                1 ⊓ Fin.toℕ remainder + quotient + (1 ⊔ o) + (d + o)
            ≤⟨ +n-mono (d + o)
                (+n-mono (1 ⊔ o)
                    (+n-mono quotient
                        (m⊓n≤n 1 (Fin.toℕ remainder))))
            ⟩
                Fin.toℕ remainder + quotient + (1 ⊔ o) + (d + o)
            ≈⟨ +-assoc (Fin.toℕ remainder + quotient) (1 ⊔ o) (d + o) ⟩
                Fin.toℕ remainder + quotient + (1 ⊔ o + (d + o))
            ≈⟨ cong (λ w → Fin.toℕ remainder + quotient + w) (+-comm (1 ⊔ o) (d + o)) ⟩
                Fin.toℕ remainder + quotient + (d + o + (1 ⊔ o))
            ≤⟨ +n-mono (d + o + (1 ⊔ o))
                (n+-mono (Fin.toℕ remainder) (m≤m*1+n quotient (suc b)))
            ⟩
                Fin.toℕ remainder + quotient * base + (d + o + (1 ⊔ o))
            ≤⟨ n+-mono (Fin.toℕ remainder + quotient * base)
                (n+-mono (d + o)
                    (m≤m*1+n (1 ⊔ o) (suc b)))
            ⟩
                Fin.toℕ remainder + quotient * base + (d + o + (1 ⊔ o) * base)
            ≈⟨ cong (λ w → w + (d + o + (1 ⊔ o) * base)) (sym divModProp) ⟩
                sum o x y ∸ (d + o + (1 ⊔ o) * base) + (d + o + (1 ⊔ o) * base)
            ≈⟨ m∸n+n≡m (<⇒≤ (≰⇒> ¬within)) ⟩
                sum o x y
            ≤⟨ sum-upper-bound o x y ⟩
                d + o + (d + o)
            □

        property :
              Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
            + Digit-toℕ (Digit-fromℕ    carry o    carry-upper-bound) o * base
            ≡ sum o x y
        property =
            begin
                Digit-toℕ (Digit-fromℕ leftover o leftover-upper-bound) o
              + Digit-toℕ (Digit-fromℕ    carry o    carry-upper-bound) o * base
            ≡⟨ cong₂
                (λ l c → l + c * base)
                (Digit-toℕ-fromℕ leftover leftover-lower-bound leftover-upper-bound)
                (Digit-toℕ-fromℕ    carry    carry-lower-bound    carry-upper-bound)
            ⟩
                leftover + carry * base
            ≡⟨ refl ⟩
                sum o x y ∸ carry * base + carry * base
            ≡⟨ m∸n+n≡m $
                start
                    carry * base
                ≤⟨ m≤n+m (carry * base) o ⟩
                    o + carry * base
                ≤⟨ leftover-lower-bound-lemma remainder divModProp ⟩
                    sum o x y
                □
            ⟩
                sum o x y
            ∎

n+-Proper : ∀ {b d o}
    → (cont : True (Continuous? (suc b) (suc d) o))
    → (proper : suc d + o ≥ 2)
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → Num (suc b) (suc d) o
n+-Proper {b} {d} {o} cont proper x xs with sumView b d o ? proper x (lsd xs)
... | p = ?
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
