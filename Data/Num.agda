module Data.Num where

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
    ≤⟨ ≤-pred (Digit-upper-bound o x) +-mono ≤-pred (Digit-upper-bound o y) ⟩
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
        → (leftover carry : Digit (suc d))
        → (property : Digit-toℕ leftover o + (Digit-toℕ carry o) * suc b ≡ sum o x y)
        → Sum b d o x y
    Above : ∀ {b d o x y}
        → (leftover carry : Digit (suc d))
        → (property : Digit-toℕ leftover o + (Digit-toℕ carry o) * suc b ≡ sum o x y)
        → Sum b d o x y



sumView : ∀ b d o
    → (¬gapped : (1 ⊔ o) * suc b ≤ suc d)
    → (proper : 2 ≤ suc d + o)
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
            ≡⟨ Digit-fromℕ-toℕ (sum o x y) (sum≥o o x y) below ⟩
                sum o x y
            ∎
sumView b d o ¬gapped proper x y | no ¬below with (sum o x y) ≤? d + o + (1 ⊔ o) * (suc b)
sumView b d o ¬gapped proper x y | no ¬below | yes within
    = Within
        (Digit-fromℕ leftover o leftover-upper-bound)
        (Digit-fromℕ carry    o carry-upper-bound)
        property

    where
        base : ℕ
        base = suc b

        carry : ℕ
        carry = carry' o

        sum≥carry*base : sum o x y ≥ carry * base
        sum≥carry*base =
            start
                carry * base
            ≤⟨ m≤m+n (carry * base) o ⟩
                carry * base + o
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

        carry-lower-bound : carry ≥ o
        carry-lower-bound = carry-lower-bound'

        carry-upper-bound : carry ≤ d + o
        carry-upper-bound = carry-upper-bound' {d} {o} proper

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
                (Digit-fromℕ-toℕ leftover leftover-lower-bound leftover-upper-bound)
                (Digit-fromℕ-toℕ    carry    carry-lower-bound    carry-upper-bound)
            ⟩
                leftover + carry * base
            ≡⟨ refl ⟩
                sum o x y ∸ carry * base + carry * base
            ≡⟨ m∸n+n≡m sum≥carry*base ⟩
                sum o x y
            ∎

sumView b d o ¬gapped proper x y | no ¬below | no ¬within with (sum o x y ∸ ((d + o) + (1 ⊔ o) * (suc b))) divMod (suc b)
sumView b d o ¬gapped proper x y | no ¬below | no ¬within | result quotient remainder divModProp _ _
    = Above
        (Digit-fromℕ leftover o leftover-upper-bound)
        (Digit-fromℕ carry    o carry-upper-bound)
        property
    where

        base : ℕ
        base = suc b

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
                (n+-mono (Fin.toℕ remainder) (m≤m*1+n quotient b))
            ⟩
                Fin.toℕ remainder + quotient * base + (d + o + (1 ⊔ o))
            ≤⟨ n+-mono (Fin.toℕ remainder + quotient * base)
                (n+-mono (d + o)
                    (m≤m*1+n (1 ⊔ o) b))
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
                (Digit-fromℕ-toℕ leftover leftover-lower-bound leftover-upper-bound)
                (Digit-fromℕ-toℕ    carry    carry-lower-bound    carry-upper-bound)
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
    → (¬gapped : (1 ⊔ o) * suc b ≤ suc d)
    → (proper : suc d + o ≥ 2)
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → Num (suc b) (suc d) o
n+-Proper {b} {d} {o} ¬gapped proper x xs with sumView b d o ¬gapped proper x (lsd xs)
n+-Proper ¬gapped proper x (_ ∙)    | Below leftover property = leftover ∙
n+-Proper ¬gapped proper x (_ ∷ xs) | Below leftover property = leftover ∷ xs
n+-Proper ¬gapped proper x (_ ∙)    | Within leftover carry property = leftover ∷ carry ∙
n+-Proper ¬gapped proper x (_ ∷ xs) | Within leftover carry property = leftover ∷ n+-Proper ¬gapped proper carry xs
n+-Proper ¬gapped proper x (_ ∙)    | Above leftover carry property = leftover ∷ carry ∙
n+-Proper ¬gapped proper x (_ ∷ xs) | Above leftover carry property = leftover ∷ n+-Proper ¬gapped proper carry xs

n+-Proper-toℕ : ∀ {b d o}
    → (¬gapped : (1 ⊔ o) * suc b ≤ suc d)
    → (proper : suc d + o ≥ 2)
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → ⟦ n+-Proper ¬gapped proper x xs ⟧ ≡ Digit-toℕ x o + ⟦ xs ⟧
n+-Proper-toℕ {b} {d} {o} ¬gapped proper x xs with sumView b d o ¬gapped proper x (lsd xs)
n+-Proper-toℕ {b} {d} {o} ¬gapped proper x (_ ∙)    | Below leftover property = property
n+-Proper-toℕ {b} {d} {o} ¬gapped proper x (x' ∷ xs) | Below leftover property =
    begin
        ⟦ leftover ∷ xs ⟧
    ≡⟨ refl ⟩
        Digit-toℕ leftover o + ⟦ xs ⟧ * suc b
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) property ⟩
        Digit-toℕ x o + Digit-toℕ x' o + ⟦ xs ⟧ * suc b
    ≡⟨ +-assoc (Digit-toℕ x o) (Digit-toℕ x' o) (⟦ xs ⟧ * suc b) ⟩
        Digit-toℕ x o + ⟦ x' ∷ xs ⟧
    ∎
n+-Proper-toℕ {b} {d} {o} ¬gapped proper x (_ ∙)    | Within leftover carry property = property
n+-Proper-toℕ {b} {d} {o} ¬gapped proper x (x' ∷ xs) | Within leftover carry property =
    begin
        ⟦ leftover ∷ n+-Proper ¬gapped proper carry xs ⟧
    ≡⟨ refl ⟩
        Digit-toℕ leftover o + ⟦ n+-Proper ¬gapped proper carry xs ⟧ * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + w * suc b) (n+-Proper-toℕ ¬gapped proper carry xs) ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o + ⟦ xs ⟧) * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + w) (distribʳ-*-+ (suc b) (Digit-toℕ carry o) ⟦ xs ⟧) ⟩
        Digit-toℕ leftover o + ((Digit-toℕ carry o) * suc b + ⟦ xs ⟧ * suc b)
    ≡⟨ sym (+-assoc (Digit-toℕ leftover o) ((Digit-toℕ carry o) * suc b) (⟦ xs ⟧ * suc b)) ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o) * suc b + ⟦ xs ⟧ * suc b
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) property ⟩
        Digit-toℕ x o + Digit-toℕ x' o + ⟦ xs ⟧ * suc b
    ≡⟨ +-assoc (Digit-toℕ x o) (Digit-toℕ x' o) (⟦ xs ⟧ * suc b) ⟩
        Digit-toℕ x o + (Digit-toℕ x' o + ⟦ xs ⟧ * suc b)
    ∎
n+-Proper-toℕ {b} {d} {o} ¬gapped proper x (_ ∙)    | Above leftover carry property = property
n+-Proper-toℕ {b} {d} {o} ¬gapped proper x (x' ∷ xs) | Above leftover carry property =
    begin
        ⟦ leftover ∷ n+-Proper ¬gapped proper carry xs ⟧
    ≡⟨ refl ⟩
        Digit-toℕ leftover o + ⟦ n+-Proper ¬gapped proper carry xs ⟧ * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + w * suc b) (n+-Proper-toℕ ¬gapped proper carry xs) ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o + ⟦ xs ⟧) * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + w) (distribʳ-*-+ (suc b) (Digit-toℕ carry o) ⟦ xs ⟧) ⟩
        Digit-toℕ leftover o + ((Digit-toℕ carry o) * suc b + ⟦ xs ⟧ * suc b)
    ≡⟨ sym (+-assoc (Digit-toℕ leftover o) ((Digit-toℕ carry o) * suc b) (⟦ xs ⟧ * suc b)) ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o) * suc b + ⟦ xs ⟧ * suc b
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) property ⟩
        Digit-toℕ x o + Digit-toℕ x' o + ⟦ xs ⟧ * suc b
    ≡⟨ +-assoc (Digit-toℕ x o) (Digit-toℕ x' o) (⟦ xs ⟧ * suc b) ⟩
        Digit-toℕ x o + (Digit-toℕ x' o + ⟦ xs ⟧ * suc b)
    ∎

data N+Closed : (b d o : ℕ) → Set where
    IsContinuous : ∀ {b d o} → (cont : True (Continuous? b d o)) → N+Closed b d o
    ℤₙ : ∀ {o} → N+Closed 1 1 o

n+-ℤₙ : ∀ {o}
    → (n : Digit 1)
    → (xs : Num 1 1 (o))
    → Num 1 1 o
n+-ℤₙ n xs = n ∷ xs

n+-ℤₙ-toℕ : ∀ {o}
    → (n : Digit 1)
    → (xs : Num 1 1 o)
    → ⟦ n+-ℤₙ n xs ⟧ ≡ Digit-toℕ n o + ⟦ xs ⟧
n+-ℤₙ-toℕ {o} n xs =
    begin
        Fin.toℕ n + o + ⟦ xs ⟧ * suc zero
    ≡⟨ cong (λ w → Fin.toℕ n + o + w) (*-right-identity ⟦ xs ⟧) ⟩
        Fin.toℕ n + o + ⟦ xs ⟧
    ∎

n+ : ∀ {b d o}
    → {cond : N+Closed b d o}
    → (n : Digit d)
    → (xs : Num b d o)
    → Num b d o
n+ {b} {d} {o} {IsContinuous cont} n xs with numView b d o
n+ {_} {_} {_} {IsContinuous ()}   n xs | NullBase d o
n+ {_} {_} {_} {IsContinuous cont} n xs | NoDigits b o = NoDigits-explode xs
n+ {_} {_} {_} {IsContinuous ()}   n xs | AllZeros b
n+ {_} {_} {_} {IsContinuous cont} n xs | Proper b d o proper with Gapped#0? b d o
n+ {_} {_} {_} {IsContinuous ()}   n xs | Proper b d o proper | yes gapped#0
n+ {_} {_} {_} {IsContinuous cont} n xs | Proper b d o proper | no ¬gapped#0 = n+-Proper (≤-pred (≰⇒> ¬gapped#0)) proper n xs
n+ {_} {_} {_} {ℤₙ}                n xs = n+-ℤₙ n xs

n+-toℕ : ∀ {b d o}
    → {cond : N+Closed b d o}
    → (n : Digit d)
    → (xs : Num b d o)
    → ⟦ n+ {cond = cond} n xs ⟧ ≡ Digit-toℕ n o + ⟦ xs ⟧
n+-toℕ {b} {d} {o} {IsContinuous cont} n xs with numView b d o
n+-toℕ {_} {_} {_} {IsContinuous ()}   n xs | NullBase d o
n+-toℕ {_} {_} {_} {IsContinuous cont} n xs | NoDigits b o = NoDigits-explode xs
n+-toℕ {_} {_} {_} {IsContinuous ()}   n xs | AllZeros b
n+-toℕ {_} {_} {_} {IsContinuous cont} n xs | Proper b d o proper with Gapped#0? b d o
n+-toℕ {_} {_} {_} {IsContinuous ()}   n xs | Proper b d o proper | yes gapped#0
n+-toℕ {_} {_} {_} {IsContinuous cont} n xs | Proper b d o proper | no ¬gapped#0 = n+-Proper-toℕ (≤-pred (≰⇒> ¬gapped#0)) proper n xs
n+-toℕ {_} {_} {_} {ℤₙ}                n xs = n+-ℤₙ-toℕ n xs

Isℤₙ : (b d o : ℕ) → Set
Isℤₙ zero d o = ⊥
Isℤₙ (suc zero) zero o = ⊥
Isℤₙ (suc zero) (suc zero) zero = {!   !}
Isℤₙ (suc zero) (suc zero) (suc o) = {!   !}
Isℤₙ (suc zero) (suc (suc d)) o = {!   !}
Isℤₙ (suc (suc b)) d o = ⊥
-- Isℤₙ b zero o = ⊥
-- Isℤₙ b (suc zero) o = {!   !}
-- Isℤₙ b (suc (suc d)) o = ⊥

-- closedness-lemma : ∀ {b d o}
--     → {¬ℤₙ : }
--     → {¬cont : False (Continuous? b d o)}
--     → {¬cont : False (Continuous? b d o)}
--     → (n : Digit d)
--     → (xs : Num b d o)



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

-- _⊹_ : ∀ {b d o}
--     → {cont : True (Continuous? b d o)}
--     → (xs ys : Num b d o)
--     → Num b d o
-- _⊹_ {b} {d} {o} {cont} (x ∙)    ys    = n+ {cont = cont} x ys
-- _⊹_ {b} {d} {o} {cont} (x ∷ xs) ys    = n+ {cont = cont} x (_⊹_ {cont = cont} xs ys)




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
--     ≤⟨ ≤-pred (Digit-upper-bound x o) ⟩
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
