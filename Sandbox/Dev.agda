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

data Sum : (b d o : ℕ) (y x : Digit (suc d)) → Set where
    Before : ∀ {b d o y x}
        → (remainder : Digit (suc d))
        → (property : Digit-toℕ remainder o ≡ sum o y x)
        → Sum b d o y x
    Between : ∀ {b d o y x}
        → (remainder carry : Digit (suc d))
        → (property : Digit-toℕ remainder o + (Digit-toℕ carry o) * suc b ≡ sum o y x)
        → Sum b d o y x
    After : ∀ {b d o y x}
        → (remainder carry : Digit (suc d))
        → (property : Digit-toℕ remainder o + (Digit-toℕ carry o) * suc b ≡ sum o y x)
        → Sum b d o y x

sumView : ∀ b d o
    → (cont : True (Continuous? (suc b) (suc d) o))
    → (proper : suc d + o ≥ 2)
    → (y : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → Sum b d o y (lsd xs)
sumView b d o cont proper y xs with (sum o y (lsd xs)) ≤? d + o
sumView b d o cont proper y xs | yes p
    = Before
        (Digit-fromℕ (sum o y (lsd xs)) o remainder-upper-bound)
        property
    where
        remainder : ℕ
        remainder = sum o y (lsd xs)

        remainder-upper-bound : remainder ≤ d + o
        remainder-upper-bound = p

        property :
              Digit-toℕ (Digit-fromℕ remainder o remainder-upper-bound) o
            ≡ sum o y (lsd xs)
        property =
            begin
                Digit-toℕ (Digit-fromℕ (sum o y (lsd xs)) o p) o
            ≡⟨ Digit-toℕ-fromℕ (sum o y (lsd xs)) (sum≥o o y (lsd xs)) p ⟩
                sum o y (lsd xs)
            ∎

sumView b d o cont proper y xs | no ¬p with (sum o y (lsd xs)) ≤? o + (1 ⊔ o) * suc b
sumView b d o cont proper y xs | no ¬p | yes q
    = Between
        (Digit-fromℕ remainder o remainder-upper-bound)
        (Digit-fromℕ carry     o carry-upper-bound)
        property
    where
        sum≥carried : sum o y (lsd xs) ≥ (1 ⊔ o) * suc b
        sum≥carried =
                start
                    (1 ⊔ o) * suc b
                ≤⟨ ≤-pred (≰⇒> (Continuous⇒¬Gapped#0 cont proper)) ⟩
                    suc d
                ≤⟨ s≤s (m≤m+n d o) ⟩
                    suc (d + o)
                ≤⟨ ≰⇒> ¬p ⟩
                    sum o y (lsd xs)
                □
        remainder : ℕ
        remainder = sum o y (lsd xs) ∸ (1 ⊔ o) * suc b

        remainder-lower-bound : remainder ≥ o
        remainder-lower-bound = +n-mono-inverse ((1 ⊔ o) * suc b) $
            start
                o + (1 ⊔ o) * suc b
            ≤⟨ n+-mono o (≤-pred $ ≰⇒> (Continuous⇒¬Gapped#0 cont proper)) ⟩
                o + suc d
            ≈⟨ +-comm o (suc d) ⟩
                suc (d + o)
            ≤⟨ ≰⇒> ¬p ⟩
                sum o y (lsd xs)
            ≈⟨ sym (m∸n+n≡m sum≥carried) ⟩
                remainder + (1 ⊔ o) * suc b
            □

        remainder-upper-bound : remainder ≤ d + o
        remainder-upper-bound = +n-mono-inverse ((1 ⊔ o) * suc b) $
            start
                sum o y (lsd xs) ∸ (1 ⊔ o) * suc b + (1 ⊔ o) * suc b
            ≈⟨ m∸n+n≡m sum≥carried ⟩
                sum o y (lsd xs)
            ≤⟨ q ⟩
                o + (1 ⊔ o) * suc b
            ≤⟨ m≤n+m (o + (1 ⊔ o) * suc b) d ⟩
                d + (o + (1 ⊔ o) * suc b)
            ≈⟨ sym (+-assoc d o ((1 ⊔ o) * suc b)) ⟩
                d + o + (1 ⊔ o) * suc b
            □

        carry : ℕ
        carry = 1 ⊔ o

        carry-lower-bound : carry ≥ o
        carry-lower-bound =
            start
                o
            ≤⟨ m≤m⊔n o 1 ⟩
                o ⊔ 1
            ≈⟨ ⊔-comm o 1 ⟩
                1 ⊔ o
            □

        carry-upper-bound : carry ≤ d + o
        carry-upper-bound = ⊔-upper-bound d o 1 (≤-pred proper)

        property :
              Digit-toℕ (Digit-fromℕ remainder o remainder-upper-bound) o
            + Digit-toℕ (Digit-fromℕ carry o carry-upper-bound) o * suc b
            ≡ sum o y (lsd xs)
        property =
            begin
                Digit-toℕ (Digit-fromℕ remainder o remainder-upper-bound) o +
                Digit-toℕ (Digit-fromℕ carry o carry-upper-bound) o * suc b
            ≡⟨ cong₂
                (λ r c → r + c * suc b)
                (Digit-toℕ-fromℕ remainder remainder-lower-bound remainder-upper-bound)
                (Digit-toℕ-fromℕ carry carry-lower-bound carry-upper-bound)
            ⟩
                remainder + carry * suc b
            ≡⟨ refl ⟩
                sum o y (lsd xs) ∸ (1 ⊔ o) * suc b + (1 ⊔ o) * suc b
            ≡⟨ m∸n+n≡m sum≥carried ⟩
                sum o y (lsd xs)
            ∎
sumView b d o cont proper y xs | no ¬p | no ¬q = {!   !}

n+-Proper : ∀ {b d o}
    → (cont : True (Continuous? (suc b) (suc d) o))
    → (proper : suc d + o ≥ 2)
    → (y : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → Num (suc b) (suc d) o
n+-Proper {b} {d} {o} cont proper y xs with sumView b d o cont proper y xs
n+-Proper cont proper y (x ∙)    | Before remainder property = remainder ∙
n+-Proper cont proper y (x ∷ xs) | Before remainder property = remainder ∷ xs
n+-Proper cont proper y (x ∙)    | Between remainder carry property = remainder ∷ carry ∙
n+-Proper cont proper y (x ∷ xs) | Between remainder carry property = remainder ∷ n+-Proper cont proper carry xs
n+-Proper cont proper y xs | After remainder carry property = {!   !}


n+-Proper-toℕ : ∀ {b d o}
    → (cont : True (Continuous? (suc b) (suc d) o))
    → (proper : suc d + o ≥ 2)
    → (y : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → ⟦ n+-Proper cont proper y xs ⟧ ≡ Digit-toℕ y o + ⟦ xs ⟧
n+-Proper-toℕ {b} {d} {o} cont proper y xs with sumView b d o cont proper y xs
n+-Proper-toℕ {b} {d} {o} cont proper y (x ∙) | Before remainder property = property
n+-Proper-toℕ {b} {d} {o} cont proper y (x ∷ xs) | Before remainder property =
    begin
        Digit-toℕ remainder o + ⟦ xs ⟧ * suc b
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) property ⟩
        sum o y x + ⟦ xs ⟧ * suc b
    ≡⟨ +-assoc (Digit-toℕ y o) (Digit-toℕ x o) (⟦ xs ⟧ * suc b) ⟩
        Digit-toℕ y o + (Digit-toℕ x o + ⟦ xs ⟧ * suc b)
    ∎
n+-Proper-toℕ {b} {d} {o} cont proper y (x ∙) | Between remainder carry property = property
n+-Proper-toℕ {b} {d} {o} cont proper y (x ∷ xs) | Between remainder carry property =
    begin
        Digit-toℕ remainder o + ⟦ n+-Proper cont proper carry xs ⟧ * suc b
    ≡⟨ cong (λ w → Digit-toℕ remainder o + w * suc b) (n+-Proper-toℕ cont proper carry xs) ⟩
        Digit-toℕ remainder o + (Digit-toℕ carry o + ⟦ xs ⟧) * suc b
    ≡⟨ cong (λ w → Digit-toℕ remainder o + w) (distribʳ-*-+ (suc b) (Digit-toℕ carry o) ⟦ xs ⟧) ⟩
        Digit-toℕ remainder o + (Digit-toℕ carry o * suc b + ⟦ xs ⟧ * suc b)
    ≡⟨ sym (+-assoc (Digit-toℕ remainder o) (Digit-toℕ carry o * suc b) (⟦ xs ⟧ * suc b)) ⟩
        Digit-toℕ remainder o + Digit-toℕ carry o * suc b + ⟦ xs ⟧ * suc b
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) property ⟩
        sum o y x + ⟦ xs ⟧ * suc b
    ≡⟨ +-assoc (Digit-toℕ y o) (Digit-toℕ x o) (⟦ xs ⟧ * suc b) ⟩
        Digit-toℕ y o + ⟦ x ∷ xs ⟧
    ∎
n+-Proper-toℕ {b} {d} {o} cont proper y xs | After remainder carry property = {!   !}
