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

next-number-suc-NullBase : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ next-number-NullBase xs ¬max ⟧ ≡ suc ⟦ xs ⟧
next-number-suc-NullBase {d} {o} xs ¬max with NullBase-view d o
next-number-suc-NullBase {_} {_} xs       ¬max | AllZeros = contradiction (Maximum-AllZeros xs) ¬max
next-number-suc-NullBase {d} {o} xs       ¬max | Others bound with Greatest? (lsd xs)
next-number-suc-NullBase {d} {o} xs       ¬max | Others bound | yes greatest = contradiction (Maximum-NullBase-Greatest xs greatest) ¬max
next-number-suc-NullBase {d} {o} (x ∙)    ¬max | Others bound | no ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o
    ≡⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Fin.toℕ x + o)
    ∎
next-number-suc-NullBase {d} {o} (x ∷ xs) ¬max | Others bound | no ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * zero
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * zero) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Fin.toℕ x + o + ⟦ xs ⟧ * zero)
    ∎

-- ⟦ z ∷ LCD d o d+o≥2 ∙ ⟧ > suc ⟦ x ∙ ⟧
next-number-suc-Others-Gapped-Single : ∀ {b d o}
    → (x : Digit (suc d))
    → (greatest : Greatest x)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (gapped : Gapped {b} (x ∙) d+o≥2)
    → o + (Digit-toℕ (LCD d o d+o≥2) o) * suc b > suc (Digit-toℕ x o)
next-number-suc-Others-Gapped-Single {b} {d} {o} x greatest d+o≥2 gapped = proof
    where
        next : Num (suc b) (suc d) o
        next = z ∷ LCD d o d+o≥2 ∙

        proof : ⟦ next ⟧ > suc (Digit-toℕ x o)
        proof = start
                suc (suc (Fin.toℕ x + o))
            ≈⟨ cong (λ w → suc w + o) greatest ⟩
                suc (suc d) + o
            ≈⟨ +-comm (suc (suc d)) o ⟩
                o + suc (suc d)
            ≤⟨ n+-mono o gapped ⟩
                o + (suc zero ⊔ o) * suc b
            ≈⟨ cong (λ w → o + w * suc b) (sym (LCD-toℕ d o d+o≥2)) ⟩
                o + (Digit-toℕ (LCD d o d+o≥2) o) * suc b
            □

-- ⟦ digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ LCD d o d+o≥2 ∙ ⟧ ≡ suc ⟦ x ∙ ⟧
next-number-suc-Others-¬Gapped-Single : ∀ {b d o}
    → (x : Digit (suc d))
    → (greatest : Greatest x)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (¬gapped : ¬ (Gapped {b} (x ∙) d+o≥2))
    → Digit-toℕ (digit+1-n x greatest (gap {b} (x ∙) d+o≥2) (gap>0 (x ∙) d+o≥2)) o
        + Digit-toℕ (LCD d o d+o≥2) o * suc b ≡ suc (Digit-toℕ x o)
next-number-suc-Others-¬Gapped-Single {b} {d} {o} x greatest d+o≥2 ¬gapped = proof
    where
        lower-bound : gap (x ∙) d+o≥2 > 0
        lower-bound = gap>0 (x ∙) d+o≥2

        upper-bound : gap (x ∙) d+o≥2 ≤ suc d
        upper-bound = ≤-pred $ ≰⇒> ¬gapped

        upper-bound' : gap (x ∙) d+o≥2 ≤ suc (Fin.toℕ x + o)
        upper-bound' = start
                (1 ⊔ o) * suc b
            ≤⟨ upper-bound ⟩
                suc d
            ≈⟨ sym greatest ⟩
                suc (Fin.toℕ x)
            ≤⟨ m≤m+n (suc (Fin.toℕ x)) o ⟩
                suc (Fin.toℕ x + o)
            □

        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest (gap (x ∙) d+o≥2) lower-bound ∷ LCD d o d+o≥2 ∙

        proof : ⟦ next ⟧ ≡ suc (Digit-toℕ x o)
        proof =
            begin
                Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + Digit-toℕ (LCD d o d+o≥2) o * suc b
            ≡⟨ cong (λ w → Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + w * suc b) (LCD-toℕ d o d+o≥2) ⟩
                Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + (1 ⊔ o) * suc b
            ≡⟨ cong (λ w → w + (1 ⊔ o) * suc b) (Digit-toℕ-digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound upper-bound) ⟩
                suc (Fin.toℕ x + o) ∸ (1 ⊔ o) * suc b + (1 ⊔ o) * suc b
            ≡⟨ m∸n+n≡m upper-bound' ⟩
                suc (Digit-toℕ x o)
            ∎


-- ⟦ z ∷ next-number-Proper xs (Maximum-Proper xs d+o≥2) d+o≥2 ⟧ > suc ⟦ x ∷ xs ⟧
next-number-suc-Others-Gapped : ∀ {b d o}
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → (greatest : Greatest x)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (gapped : Gapped (x ∷ xs) d+o≥2)
    → o + ⟦ next-number-Proper xs d+o≥2 ⟧ * suc b > suc ⟦ x ∷ xs ⟧
next-number-suc-Others-Gapped {b} {d} {o} x xs greatest d+o≥2 gapped = proof
    where
        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Proper xs d+o≥2

        next-xs>xs : ⟦ next-xs ⟧ > ⟦ xs ⟧
        next-xs>xs = next-number-is-greater-Proper xs d+o≥2

        next : Num (suc b) (suc d) o
        next = z ∷ next-xs

        proof : ⟦ next ⟧ > suc ⟦ x ∷ xs ⟧
        proof = start
                suc (suc (Digit-toℕ x o)) + ⟦ xs ⟧ * suc b
            ≈⟨ cong (λ w → suc (suc w) + ⟦ xs ⟧ * suc b) (toℕ-greatest x greatest) ⟩
                suc (suc d) + o + ⟦ xs ⟧ * suc b
            ≈⟨ +-assoc (suc (suc d)) o (⟦ xs ⟧ * suc b) ⟩
                suc (suc d) + (o + ⟦ xs ⟧ * suc b)
            ≈⟨ a+[b+c]≡b+[a+c] (suc (suc d)) o (⟦ xs ⟧ * suc b) ⟩
                o + (suc (suc d) + ⟦ xs ⟧ * suc b)
            ≤⟨ n+-mono o (+n-mono (⟦ xs ⟧ * suc b) gapped) ⟩
                o + ((⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b + ⟦ xs ⟧ * suc b)
            ≈⟨ cong (λ w → o + w) (sym (distribʳ-*-+ (suc b) (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) ⟦ xs ⟧)) ⟩
                o + (⟦ next-xs ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧) * suc b
            ≈⟨ cong (λ w → o + w * suc b) (m∸n+n≡m (<⇒≤ next-xs>xs)) ⟩
                o + ⟦ next-xs ⟧ * suc b
            ≈⟨ refl ⟩
                ⟦ z ∷ next-xs ⟧
            □

-- ⟦ digit+1-n x greatest gap gap>0 ∷ next ∙ ⟧ ≡ suc ⟦ x ∷ xs ⟧
next-number-suc-Others-¬Gapped : ∀ {b d o}
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → (greatest : Greatest x)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → let
        ¬max-xs = Maximum-Proper xs d+o≥2
        next-xs = next-number-Proper xs d+o≥2
        next = digit+1-n x greatest (gap (x ∷ xs) d+o≥2) (gap>0 (x ∷ xs) d+o≥2) ∷ next-xs
      in
      (¬gapped : ¬ (Gapped (x ∷ xs) d+o≥2))
    → ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
next-number-suc-Others-¬Gapped {b} {d} {o} x xs greatest d+o≥2 ¬gapped = proof
    where
        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = Maximum-Proper xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Proper xs d+o≥2

        lower-bound : gap (x ∷ xs) d+o≥2 > 0
        lower-bound = gap>0 (x ∷ xs) d+o≥2

        upper-bound : gap (x ∷ xs) d+o≥2 ≤ suc d
        upper-bound = ≤-pred $ ≰⇒> ¬gapped

        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest (gap (x ∷ xs) d+o≥2) lower-bound ∷ next-xs

        ⟦next-xs⟧>⟦xs⟧ : ⟦ next-xs ⟧ > ⟦ xs ⟧
        ⟦next-xs⟧>⟦xs⟧ = next-number-is-greater-Proper xs d+o≥2

        upper-bound' : ⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b ≤ suc (Digit-toℕ x o)
        upper-bound' =
            start
                ⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b
            ≈⟨ sym (*-distrib-∸ʳ (suc b) ⟦ next-xs ⟧ ⟦ xs ⟧) ⟩
                (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
            ≤⟨ upper-bound ⟩
                suc d
            ≤⟨ m≤m+n (suc d) o ⟩
                suc d + o
            ≈⟨ cong (λ w → w + o) (sym greatest) ⟩
                suc (Digit-toℕ x o)
            □

        proof : ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
        proof =
            begin
                ⟦ next ⟧
            ≡⟨ cong (λ w → w + ⟦ next-xs ⟧ * suc b) (Digit-toℕ-digit+1-n x greatest (gap (x ∷ xs) d+o≥2) lower-bound upper-bound) ⟩
                suc (Digit-toℕ x o) ∸ gap (x ∷ xs) d+o≥2 + ⟦ next-xs ⟧ * suc b
            ≡⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + ⟦ next-xs ⟧ * suc b) (*-distrib-∸ʳ (suc b) ⟦ next-xs ⟧ ⟦ xs ⟧) ⟩
                suc (Digit-toℕ x o) ∸ (⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b) + ⟦ next-xs ⟧ * suc b
            ≡⟨ m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ xs ⟧ * suc b) (⟦ next-xs ⟧ * suc b) (*n-mono (suc b) (<⇒≤ ⟦next-xs⟧>⟦xs⟧)) upper-bound' ⟩
                suc ⟦ x ∷ xs ⟧
            ∎

next-number-Others-¬Incrementable-lemma : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ⟦ next-number-Proper xs d+o≥2 ⟧ > suc ⟦ xs ⟧
    → ¬ (Incrementable xs)
next-number-Others-¬Incrementable-lemma {b} {d} {o} xs d+o≥2 prop (incremented , claim)
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
            ≤⟨ prop ⟩
                ⟦ next-number-Proper xs d+o≥2 ⟧
            □
        ⟦next⟧≯⟦incremented⟧ : ⟦ next ⟧ ≯ ⟦ incremented ⟧
        ⟦next⟧≯⟦incremented⟧ = ≤⇒≯ $ next-number-is-LUB-Proper xs incremented d+o≥2 (m≡1+n⇒m>n claim)

Incrementable?-Proper : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → Dec (Incrementable xs)
Incrementable?-Proper xs d+o≥2 with nextView xs d+o≥2 | next-number-Others-¬Incrementable-lemma xs d+o≥2
Incrementable?-Proper xs    d+o≥2 | NeedNoCarry b d o ¬greatest | lemma
    = yes ((next-number-Proper xs d+o≥2) , (begin
            ⟦ next-number-Proper xs d+o≥2 ⟧
        ≡⟨ cong ⟦_⟧ (next-number-Proper-NeedNoCarry-redirect xs ¬greatest d+o≥2) ⟩
            ⟦ next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2 ⟧
        ≡⟨ next-number-Proper-NeedNoCarry-lemma xs ¬greatest d+o≥2 ⟩
            suc ⟦ xs ⟧
        ∎))
Incrementable?-Proper (x ∙)    d+o≥2 | IsGapped b d o greatest gapped | lemma
    = no (lemma (next-number-suc-Others-Gapped-Single x greatest d+o≥2 gapped))
Incrementable?-Proper (x ∷ xs) d+o≥2 | IsGapped b d o greatest gapped | lemma
    = no (lemma (next-number-suc-Others-Gapped x xs greatest d+o≥2 gapped))
Incrementable?-Proper (x ∙)    d+o≥2 | NotGapped b d o greatest ¬gapped | lemma
    = yes (
        digit+1-n x greatest (gap (x ∙) d+o≥2) (gap>0 (x ∙) d+o≥2) ∷ LCD d o d+o≥2 ∙
    ,   next-number-suc-Others-¬Gapped-Single x greatest d+o≥2 ¬gapped
    )
Incrementable?-Proper (x ∷ xs) d+o≥2 | NotGapped b d o greatest ¬gapped | lemma
    = yes (next , next-number-suc-Others-¬Gapped x xs greatest d+o≥2 ¬gapped)
    where
        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = Maximum-Proper xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Proper xs d+o≥2

        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest (gap (x ∷ xs) d+o≥2) (gap>0 (x ∷ xs) d+o≥2) ∷ next-xs

Incrementable? : ∀ {b d o}
    → (xs : Num b d o)
    → Dec (Incrementable xs)
Incrementable? xs with Maximum? xs
Incrementable? xs | yes max = no (Maximum⇒¬Incrementable xs max)
Incrementable? {b} {d} {o} xs | no ¬max with numView b d o
Incrementable? xs | no ¬max | NullBase d o
    = yes ((next-number-NullBase xs ¬max) , (next-number-suc-NullBase xs ¬max))
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
increment-next-number-Proper xs       d+o≥2 incr with nextView xs d+o≥2
increment-next-number-Proper xs       d+o≥2 incr | NeedNoCarry b d o ¬greatest = begin
        next-number-Proper xs d+o≥2
    ≡⟨ next-number-Proper-NeedNoCarry-redirect xs ¬greatest d+o≥2 ⟩
        next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2
    ∎
increment-next-number-Proper (x ∙)    d+o≥2 ()   | IsGapped b d o greatest gapped
increment-next-number-Proper (x ∷ xs) d+o≥2 ()   | IsGapped b d o greatest gapped
increment-next-number-Proper (x ∙)    d+o≥2 incr | NotGapped b d o greatest ¬gapped = refl
increment-next-number-Proper (x ∷ xs) d+o≥2 incr | NotGapped b d o greatest ¬gapped = refl

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


subsume-¬Gapped-prim : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (¬gapped : suc (suc d) > (1 ⊔ o) * suc b)
    → 1 ⊔ o ≥ ⟦ next-number-Proper xs d+o≥2 ⟧ ∸ ⟦ xs ⟧
subsume-¬Gapped-prim xs d+o≥2 ¬gapped with nextView xs d+o≥2
subsume-¬Gapped-prim xs d+o≥2 ¬gapped | NeedNoCarry b d o ¬greatest =
    start
        ⟦ next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2 ⟧ ∸ ⟦ xs ⟧
    ≈⟨ cong (λ w → w ∸ ⟦ xs ⟧) (next-number-Proper-NeedNoCarry-lemma xs ¬greatest d+o≥2) ⟩
        suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
    ≈⟨ m+n∸n≡m (suc zero) ⟦ xs ⟧ ⟩
        suc zero
    ≤⟨ m≤m⊔n 1 o ⟩
        suc zero ⊔ o
    □
subsume-¬Gapped-prim (x ∙) d+o≥2 ¬gapped | IsGapped b d o greatest gapped
    = contradiction gapped (>⇒≰ ¬gapped)
subsume-¬Gapped-prim (x ∷ xs) d+o≥2 ¬gapped | IsGapped b d o greatest gapped
    = contradiction refl (<⇒≢ p)
    where
        p : (suc zero ⊔ o) * suc b < (suc zero ⊔ o) * suc b
        p =
            start
                suc ((suc zero ⊔ o) * suc b)
            ≤⟨ ¬gapped ⟩
                suc (suc d)
            ≤⟨ gapped ⟩
                (⟦ next-number-Proper xs d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
            ≤⟨ *n-mono (suc b) (subsume-¬Gapped-prim xs d+o≥2 ¬gapped) ⟩
                (suc zero ⊔ o) * suc b
            □
subsume-¬Gapped-prim (x ∙) d+o≥2 _ | NotGapped b d o greatest ¬gapped =
    start
        ⟦ digit+1-n x greatest (gap (x ∙) d+o≥2) (gap>0 (x ∙) d+o≥2) ∷ LCD d o d+o≥2 ∙ ⟧ ∸ Digit-toℕ x o
    ≈⟨ cong (λ w → w ∸ Digit-toℕ x o) (next-number-suc-Others-¬Gapped-Single x greatest d+o≥2 ¬gapped) ⟩
        suc (Fin.toℕ x + o) ∸ (Fin.toℕ x + o)
    ≈⟨ m+n∸n≡m (suc zero) (Fin.toℕ x + o) ⟩
        suc zero
    ≤⟨ m≤m⊔n 1 o ⟩
        suc zero ⊔ o
    □
subsume-¬Gapped-prim (x ∷ xs) d+o≥2 _ | NotGapped b d o greatest ¬gapped =
    start
        ⟦ digit+1-n x greatest (gap (x ∷ xs) d+o≥2) (gap>0 (x ∷ xs) d+o≥2) ∷ next-xs ⟧ ∸ ⟦ x ∷ xs ⟧
    ≈⟨ cong (λ w → w ∸ ⟦ x ∷ xs ⟧) (next-number-suc-Others-¬Gapped x xs greatest d+o≥2 ¬gapped) ⟩
        suc ⟦ x ∷ xs ⟧ ∸ ⟦ x ∷ xs ⟧
    ≈⟨ m+n∸n≡m (suc zero) ⟦ x ∷ xs ⟧ ⟩
        suc zero
    ≤⟨ m≤m⊔n 1 o ⟩
        suc zero ⊔ o
    □
    where
        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = Maximum-Proper xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Proper xs d+o≥2

        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest (gap (x ∷ xs) d+o≥2) (gap>0 (x ∷ xs) d+o≥2) ∷ next-xs

subsume-Gapped : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → suc (suc d) ≤ (⟦ next-number-Proper xs d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
    → suc (suc d) ≤ (1 ⊔ o) * suc b
subsume-Gapped xs d+o≥2 gapped with nextView xs d+o≥2
subsume-Gapped xs d+o≥2 gapped | NeedNoCarry b d o ¬greatest =
    start
        suc (suc d)
    ≤⟨ gapped ⟩
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
subsume-Gapped (x ∙) d+o≥2 _ | IsGapped b d o greatest gapped = gapped
subsume-Gapped (x ∷ xs) d+o≥2 _ | IsGapped b d o greatest gapped = subsume-Gapped xs d+o≥2 gapped
subsume-Gapped (x ∙) d+o≥2 gapped | NotGapped b d o greatest ¬gapped =
    start
        suc (suc d)
    ≤⟨ gapped ⟩
        (⟦ digit+1-n x greatest (gap (x ∙) d+o≥2) (gap>0 (x ∙) d+o≥2) ∷ LCD d o d+o≥2 ∙ ⟧ ∸ Digit-toℕ x o) * suc b
    ≤⟨ *n-mono (suc b) $
        start
            ⟦ digit+1-n x greatest (gap (x ∙) d+o≥2) (gap>0 (x ∙) d+o≥2) ∷ LCD d o d+o≥2 ∙ ⟧ ∸ Digit-toℕ x o
        ≈⟨ cong (λ w → w ∸ Digit-toℕ x o) (next-number-suc-Others-¬Gapped-Single x greatest d+o≥2 ¬gapped) ⟩
            suc (Fin.toℕ x + o) ∸ (Fin.toℕ x + o)
        ≈⟨ m+n∸n≡m (suc zero) (Fin.toℕ x + o) ⟩
            suc zero
        ≤⟨ m≤m⊔n 1 o ⟩
            suc zero ⊔ o
        □
    ⟩
        (suc zero ⊔ o) * suc b
    □
subsume-Gapped (x ∷ xs) d+o≥2 gapped | NotGapped b d o greatest ¬gapped =
    start
        suc (suc d)
    ≤⟨ gapped ⟩
        (⟦ digit+1-n x greatest (gap (x ∷ xs) d+o≥2) (gap>0 (x ∷ xs) d+o≥2) ∷ next-xs ⟧ ∸ ⟦ x ∷ xs ⟧) * suc b
    ≤⟨ *n-mono (suc b) $
        start
            ⟦ digit+1-n x greatest (gap (x ∷ xs) d+o≥2) (gap>0 (x ∷ xs) d+o≥2) ∷ next-xs ⟧ ∸ ⟦ x ∷ xs ⟧
        ≈⟨ cong (λ w → w ∸ ⟦ x ∷ xs ⟧) (next-number-suc-Others-¬Gapped x xs greatest d+o≥2 ¬gapped) ⟩
            suc ⟦ x ∷ xs ⟧ ∸ ⟦ x ∷ xs ⟧
        ≈⟨ m+n∸n≡m (suc zero) ⟦ x ∷ xs ⟧ ⟩
            suc zero
        ≤⟨ m≤m⊔n 1 o ⟩
            suc zero ⊔ o
        □
    ⟩
        (suc zero ⊔ o) * suc b
    □
    where
        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = Maximum-Proper xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Proper xs d+o≥2

        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest (gap (x ∷ xs) d+o≥2) (gap>0 (x ∷ xs) d+o≥2) ∷ next-xs

subsume-¬Gapped : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → suc (suc d) > (1 ⊔ o) * suc b
    → suc (suc d) > (⟦ next-number-Proper xs d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
subsume-¬Gapped {b} {d} {o} xs d+o≥2 ¬gapped =
    start
        suc ((⟦ next-number-Proper xs d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b)
    ≤⟨ s≤s (*n-mono (suc b) (subsume-¬Gapped-prim xs d+o≥2 ¬gapped)) ⟩
        suc ((suc zero ⊔ o) * suc b)
    ≤⟨ ¬gapped ⟩
        suc (suc d)
    □
