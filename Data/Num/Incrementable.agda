module Data.Num.Incrementable where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next

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

------------------------------------------------------------------------
-- a number is incrementable if there exists some n' : Num b d o such that ⟦ n' ⟧ℕ ≡ suc ⟦ n ⟧ℕ

Incrementable : ∀ {b d o} → (xs : Num b d o) → Set
Incrementable {b} {d} {o} xs = Σ[ xs' ∈ Num b d o ] ⟦ xs' ⟧ ≡ suc ⟦ xs ⟧

m≡1+n⇒m>n : ∀ {m n} → m ≡ suc n → m > n
m≡1+n⇒m>n {zero}  {n}  ()
m≡1+n⇒m>n {suc m} {.m} refl = s≤s ≤-refl

Maximum⇒¬Incrementable : ∀ {b d o}
    → (xs : Num b d o)
    → (max : Maximum xs)
    → ¬ (Incrementable xs)
Maximum⇒¬Incrementable xs max (evidence , claim)
    = contradiction (max evidence) (>⇒≰ (m≡1+n⇒m>n claim))

next-number-NullBase-lemma : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ next-number-NullBase xs ¬max ⟧ ≡ suc ⟦ xs ⟧
next-number-NullBase-lemma {d} {o} xs ¬max with NullBase-view d o
next-number-NullBase-lemma {_} {_} xs       ¬max | AllZeros = contradiction (Maximum-AllZeros xs) ¬max
next-number-NullBase-lemma {d} {o} xs       ¬max | Others bound with Greatest? (lsd xs)
next-number-NullBase-lemma {d} {o} xs       ¬max | Others bound | yes greatest = contradiction (Maximum-NullBase-Greatest xs greatest) ¬max
next-number-NullBase-lemma {d} {o} (x ∙)    ¬max | Others bound | no ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o
    ≡⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Fin.toℕ x + o)
    ∎
next-number-NullBase-lemma {d} {o} (x ∷ xs) ¬max | Others bound | no ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * zero
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * zero) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Fin.toℕ x + o + ⟦ xs ⟧ * zero)
    ∎

IsGapped⇒¬Incrementable : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (greatest : Greatest (lsd xs))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (gapped : Gapped xs d+o≥2)
    → ¬ (Incrementable xs)
IsGapped⇒¬Incrementable {b} {d} {o} xs greatest d+o≥2 gapped (incremented , claim)
    = contradiction ⟦next⟧>⟦incremented⟧ ⟦next⟧≯⟦incremented⟧
    where
        next : Num (suc b) (suc d) o
        next = next-number-Proper xs d+o≥2

        ⟦next⟧>⟦incremented⟧ : ⟦ next ⟧ > ⟦ incremented ⟧
        ⟦next⟧>⟦incremented⟧ =
            start
                suc ⟦ incremented ⟧
            ≈⟨ cong suc claim ⟩
                suc (suc ⟦ xs ⟧)
            ≤⟨ next-number-Proper-IsGapped-lemma xs greatest d+o≥2 gapped ⟩
                ⟦ next-number-Proper-IsGapped xs d+o≥2 gapped ⟧
            ≈⟨ cong ⟦_⟧ (sym (next-number-Proper-refine xs d+o≥2 (IsGapped b d o greatest gapped))) ⟩
                ⟦ next-number-Proper xs d+o≥2 ⟧
            □

        ⟦next⟧≯⟦incremented⟧ : ⟦ next ⟧ ≯ ⟦ incremented ⟧
        ⟦next⟧≯⟦incremented⟧ = ≤⇒≯ $ next-number-is-LUB-Proper xs incremented d+o≥2 (m≡1+n⇒m>n claim)




Incrementable?-Proper : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → Dec (Incrementable xs)
Incrementable?-Proper xs d+o≥2 with nextView xs d+o≥2
Incrementable?-Proper xs d+o≥2 | NeedNoCarry b d o ¬greatest
    = yes ((next-number-Proper xs d+o≥2) , (begin
            ⟦ next-number-Proper xs d+o≥2 ⟧
        ≡⟨ cong ⟦_⟧ (next-number-Proper-refine xs d+o≥2 (NeedNoCarry b d o ¬greatest)) ⟩
            ⟦ next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2 ⟧
        ≡⟨ next-number-Proper-NeedNoCarry-lemma xs ¬greatest d+o≥2 ⟩
            suc ⟦ xs ⟧
        ∎))
Incrementable?-Proper xs d+o≥2 | IsGapped b d o greatest gapped
    = no (IsGapped⇒¬Incrementable xs greatest d+o≥2 gapped)
Incrementable?-Proper xs d+o≥2 | NotGapped b d o greatest ¬gapped
    = yes ((next-number-Proper xs d+o≥2) , (begin
            ⟦ next-number-Proper xs d+o≥2 ⟧
        ≡⟨ cong ⟦_⟧ (next-number-Proper-refine xs d+o≥2 (NotGapped b d o greatest ¬gapped)) ⟩
            ⟦ next-number-Proper-NotGapped xs greatest d+o≥2 ¬gapped ⟧
        ≡⟨ next-number-Proper-NotGapped-lemma xs greatest d+o≥2 ¬gapped ⟩
            suc ⟦ xs ⟧
        ∎))


Incrementable? : ∀ {b d o}
    → (xs : Num b d o)
    → Dec (Incrementable xs)
Incrementable? xs with Maximum? xs
Incrementable? xs | yes max = no (Maximum⇒¬Incrementable xs max)
Incrementable? {b} {d} {o} xs | no ¬max with numView b d o
Incrementable? xs | no ¬max | NullBase d o
    = yes ((next-number-NullBase xs ¬max) , (next-number-NullBase-lemma xs ¬max))
Incrementable? xs | no ¬max | NoDigits b o
    = no (NoDigits-explode xs)
Incrementable? xs | no ¬max | AllZeros b
    = no (contradiction (Maximum-AllZeros xs) ¬max)
Incrementable? xs | no ¬max | Proper b d o d+o≥2
    = Incrementable?-Proper xs d+o≥2

increment : ∀ {b d o}
    → (xs : Num b d o)
    → (incr : True (Incrementable? xs))
    → Num b d o
increment xs incr = proj₁ $ toWitness incr

increment-next-number-Proper : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (incr : True (Incrementable?-Proper xs d+o≥2))
    → proj₁ (toWitness incr) ≡ next-number-Proper xs d+o≥2
increment-next-number-Proper xs d+o≥2 incr with nextView xs d+o≥2
increment-next-number-Proper xs d+o≥2 incr | NeedNoCarry b d o ¬greatest = begin
        next-number-Proper xs d+o≥2
    ≡⟨ next-number-Proper-refine xs d+o≥2 (NeedNoCarry b d o ¬greatest) ⟩
        next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2
    ∎
increment-next-number-Proper xs d+o≥2 ()   | IsGapped b d o greatest gapped
increment-next-number-Proper xs d+o≥2 incr | NotGapped b d o greatest ¬gapped = begin
        next-number-Proper xs d+o≥2
    ≡⟨ next-number-Proper-refine xs d+o≥2 (NotGapped b d o greatest ¬gapped) ⟩
        next-number-Proper-NotGapped xs greatest d+o≥2 ¬gapped
    ∎

increment-next-number : ∀ {b d o}
    → (xs : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → (incr : True (Incrementable? xs))
    → increment xs incr ≡ next-number xs ¬max
increment-next-number xs ¬max incr with Maximum? xs
increment-next-number xs ¬max () | yes max
increment-next-number {b} {d} {o} xs ¬max incr | no _  with numView b d o
increment-next-number xs _ incr | no ¬max | NullBase d o = refl
increment-next-number xs _ ()   | no ¬max | NoDigits b o
increment-next-number xs _ ()   | no ¬max | AllZeros b
increment-next-number xs _ incr | no ¬max | Proper b d o d+o≥2
    = increment-next-number-Proper xs d+o≥2 incr



Gapped#N⇒Gapped#0 : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → Gapped#N b d o xs d+o≥2
    → Gapped#0 b d o
Gapped#N⇒Gapped#0 xs d+o≥2 gapped#N with nextView xs d+o≥2
Gapped#N⇒Gapped#0 xs d+o≥2 gapped#N | NeedNoCarry b d o ¬greatest =
    start
        suc (suc d)
    ≤⟨ gapped#N ⟩
        (⟦ next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
    ≤⟨ *n-mono (suc b) $
        start
            ⟦ next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2 ⟧ ∸ ⟦ xs ⟧
        ≈⟨ cong (λ w → w ∸ ⟦ xs ⟧) (next-number-Proper-NeedNoCarry-lemma xs ¬greatest d+o≥2) ⟩
            suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
        ≈⟨ m+n∸n≡m (suc zero) ⟦ xs ⟧ ⟩
            suc zero
        ≤⟨ m≤m⊔n 1 o ⟩
            suc zero ⊔ o
        □
     ⟩
        (suc zero ⊔ o) * suc b
    □
Gapped#N⇒Gapped#0 (x ∙)    d+o≥2 gapped#N | IsGapped b d o greatest gapped#0 = gapped#0
Gapped#N⇒Gapped#0 (x ∷ xs) d+o≥2 _        | IsGapped b d o greatest gapped#N = Gapped#N⇒Gapped#0 xs d+o≥2 gapped#N
Gapped#N⇒Gapped#0 xs d+o≥2 gapped#N | NotGapped b d o greatest ¬gapped =
        start
            suc (suc d)
        ≤⟨ gapped#N ⟩
            (⟦ next-number-Proper-NotGapped xs greatest d+o≥2 ¬gapped ⟧ ∸ ⟦ xs ⟧) * suc b
        ≤⟨ *n-mono (suc b) $
            start
                ⟦ next-number-Proper-NotGapped xs greatest d+o≥2 ¬gapped ⟧ ∸ ⟦ xs ⟧
            ≈⟨ cong (λ w → w ∸ ⟦ xs ⟧) (next-number-Proper-NotGapped-lemma xs greatest d+o≥2 ¬gapped) ⟩
                suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
            ≈⟨ m+n∸n≡m (suc zero) ⟦ xs ⟧ ⟩
                suc zero
            ≤⟨ m≤m⊔n 1 o ⟩
                suc zero ⊔ o
            □
         ⟩
            (suc zero ⊔ o) * suc b
        □

¬Gapped#0⇒¬Gapped#N : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ¬ (Gapped#0 b d o)
    → ¬ (Gapped#N b d o xs d+o≥2)
¬Gapped#0⇒¬Gapped#N xs d+o≥2 ¬Gapped#0 = contraposition (Gapped#N⇒Gapped#0 xs d+o≥2) ¬Gapped#0
