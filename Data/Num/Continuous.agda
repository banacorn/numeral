module Data.Num.Continuous where

open import Data.Num.Core
open import Data.Num.Maximum
open import Data.Num.Bounded
open import Data.Num.Next
open import Data.Num.Incrementable

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

Continuous : ∀ b d o → Set
Continuous b d o = (xs : Num b d o) → Incrementable xs

Bounded⇒¬Continuous : ∀ {b d o}
    → Bounded b d o
    → ¬ (Continuous b d o)
Bounded⇒¬Continuous (xs , max) claim = contradiction (claim xs) (Maximum⇒¬Incrementable xs max)

Continuous-Others-Gapped-counter-example : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (xs ≡ greatest-digit d ∙)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (gapped : suc (suc d) ≤ (1 ⊔ o) * suc b)
    → ¬ (Incrementable {suc b} {_} {o} xs)
Continuous-Others-Gapped-counter-example {b} {d} {o} (x ∙) eq d+o≥2 gapped with Others-view-single b d o x | next-number-Others-¬Incrementable-lemma {b} (x ∙) (Maximum-Others (x ∙) d+o≥2) d+o≥2
Continuous-Others-Gapped-counter-example {b} {d} {o} (_ ∙) refl d+o≥2 gapped | NeedNoCarry ¬greatest | lemma = contradiction (greatest-digit-is-the-Greatest d) ¬greatest
Continuous-Others-Gapped-counter-example {b} {d} {o} (x ∙) eq d+o≥2 gapped | Gapped greatest _ | lemma = lemma prop
    where
        prop : o + Digit-toℕ (LCD d o d+o≥2) o * suc b > suc (Digit-toℕ x o)
        prop = next-number-suc-Others-Gapped-Single x greatest d+o≥2 gapped
Continuous-Others-Gapped-counter-example {b} {d} {o} (x ∙) eq d+o≥2 gapped | ¬Gapped greatest ¬gapped | lemma = contradiction gapped (>⇒≰ (s≤s ¬gapped))
Continuous-Others-Gapped-counter-example (x ∷ xs) () d+o≥2 gapped incr

Continuous-Others-Gapped : ∀ b d o
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (gapped : suc (suc d) ≤ (1 ⊔ o) * suc b)
    → ¬ (Continuous (suc b) (suc d) o)
Continuous-Others-Gapped b d o d+o≥2 gapped cont
    = contradiction (cont counter-example) (Continuous-Others-Gapped-counter-example (greatest-digit d ∙) refl d+o≥2 gapped)
    where
        counter-example : Num (suc b) (suc d) o
        counter-example = greatest-digit d ∙

Continuous-Others-¬Gapped : ∀ b d o
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (¬gapped : suc (suc d) ≰ (1 ⊔ o) * suc b)
    → Continuous (suc b) (suc d) o
Continuous-Others-¬Gapped b d o d+o≥2 ¬gapped (x ∙) with Others-view-single b d o x
Continuous-Others-¬Gapped b d o d+o≥2 ¬gapped (x ∙) | NeedNoCarry ¬greatest
    = next , next-number-increment
    where
        ¬max : ¬ (Maximum (x ∙))
        ¬max = Maximum-Others {b} (x ∙) d+o≥2
        next : Num (suc b) (suc d) o
        next = next-number-Others (x ∙) ¬max d+o≥2
        next-number-increment : ⟦ next-number-Others (x ∙) ¬max d+o≥2 ⟧ ≡ suc (Fin.toℕ x + o)
        next-number-increment = next-number-suc-Others-LSD-¬Greatest (x ∙) ¬max ¬greatest d+o≥2
Continuous-Others-¬Gapped b d o d+o≥2 ¬gapped (x ∙) | Gapped greatest gapped
    = contradiction gapped ¬gapped
Continuous-Others-¬Gapped b d o d+o≥2 ¬gapped (x ∙) | ¬Gapped greatest _
    = next , next-number-suc-Others-¬Gapped-Single {b} x greatest d+o≥2 (≤-pred $ ≰⇒> ¬gapped)
    where
        lower-bound : (1 ⊔ o) * suc b > 0
        lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n
        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ LCD d o d+o≥2 ∙
Continuous-Others-¬Gapped b d o d+o≥2 ¬gapped (x ∷ xs) with Others-view x xs (Maximum-Others (x ∷ xs) d+o≥2) d+o≥2
Continuous-Others-¬Gapped b d o d+o≥2 ¬gapped (x ∷ xs) | NeedNoCarry ¬greatest
    = next , proof
    where
        next : Num (suc b) (suc d) o
        next = digit+1 x ¬greatest ∷ xs

        proof : ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
        proof = cong (λ w → w + ⟦ xs ⟧ * suc b) (Digit-toℕ-digit+1 x ¬greatest)
Continuous-Others-¬Gapped b d o d+o≥2 ¬gapped (x ∷ xs) | Gapped greatest gapped
    = contradiction gapped (>⇒≰ ¬gapped')
    where
        ¬gapped' : suc (suc d) > (⟦ next-number-Others xs (Maximum-Others xs d+o≥2) d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
        ¬gapped' = subsume-¬Gapped xs d+o≥2 (≰⇒> ¬gapped)
Continuous-Others-¬Gapped b d o d+o≥2 _ (x ∷ xs) | ¬Gapped greatest ¬gapped
    = next , proof
    where
        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = Maximum-Others xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Others xs ¬max-xs d+o≥2

        gap : ℕ
        gap = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b

        lower-bound : gap > 0
        lower-bound = (start
                1
            ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ xs ⟧))) ⟩
                suc (⟦ xs ⟧ ∸ ⟦ xs ⟧)
            ≈⟨ sym (+-∸-assoc 1 {⟦ xs ⟧} ≤-refl) ⟩
                suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
            ≤⟨ ∸-mono {suc ⟦ xs ⟧} {⟦ next-xs ⟧} {⟦ xs ⟧} (next-number-is-greater-Others xs ¬max-xs d+o≥2) ≤-refl ⟩
                ⟦ next-xs ⟧ ∸ ⟦ xs ⟧
            □) *-mono (s≤s {0} {b} z≤n)

        upper-bound : gap ≤ suc d
        upper-bound = ¬gapped

        next : Num (suc b) (suc d) o
        next = digit+1-n x greatest gap lower-bound ∷ next-xs

        ⟦next-xs⟧>⟦xs⟧ : ⟦ next-xs ⟧ > ⟦ xs ⟧
        ⟦next-xs⟧>⟦xs⟧ = next-number-is-greater-Others xs ¬max-xs d+o≥2

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
            ≡⟨ cong (λ w → w + ⟦ next-xs ⟧ * suc b) (Digit-toℕ-digit+1-n x greatest gap lower-bound upper-bound) ⟩
                suc (Digit-toℕ x o) ∸ gap + ⟦ next-xs ⟧ * suc b
            ≡⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + ⟦ next-xs ⟧ * suc b) (*-distrib-∸ʳ (suc b) ⟦ next-xs ⟧ ⟦ xs ⟧) ⟩
                suc (Digit-toℕ x o) ∸ (⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b) + ⟦ next-xs ⟧ * suc b
            ≡⟨ m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ xs ⟧ * suc b) (⟦ next-xs ⟧ * suc b) (*n-mono (suc b) (<⇒≤ ⟦next-xs⟧>⟦xs⟧)) upper-bound' ⟩
                suc ⟦ x ∷ xs ⟧
            ∎

Continuous-Others : ∀ b d o
    → (d+o≥2 : 2 ≤ suc (d + o))
    → Dec (Continuous (suc b) (suc d) o)
Continuous-Others b d o d+o≥2 with suc (suc d) ≤? (1 ⊔ o) * suc b
Continuous-Others b d o d+o≥2 | yes gapped = no (Continuous-Others-Gapped b d o d+o≥2 gapped)
Continuous-Others b d o d+o≥2 | no ¬gapped = yes (Continuous-Others-¬Gapped b d o d+o≥2 ¬gapped)

Continuous? : ∀ b d o → Dec (Continuous b d o)
Continuous? b d o with numView b d o
Continuous? _ _ _ | NullBase d o = no (Bounded⇒¬Continuous (Bounded-NullBase d o))
Continuous? _ _ _ | NoDigits b o = yes (λ xs → NoDigits-explode xs)
Continuous? _ _ _ | AllZeros b = no (Bounded⇒¬Continuous (Bounded-AllZeros b))
Continuous? _ _ _ | Others b d o d+o≥2 = Continuous-Others b d o d+o≥2
