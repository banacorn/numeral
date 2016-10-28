module Data.Num.Next where

open import Data.Num.Core
open import Data.Num.Maximum
open import Data.Num.Bounded

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

data NullBase-View : ℕ → ℕ → Set where
    AllZeros :                                   NullBase-View 0 0
    Others   : ∀ {d o} → (bound : d + o ≥ 1 ⊔ o) → NullBase-View d o

NullBase-view : ∀ d o → NullBase-View d o
NullBase-view zero    zero     = AllZeros
NullBase-view zero    (suc o)  = Others (s≤s ≤-refl)
NullBase-view (suc d) zero     = Others (s≤s z≤n)
NullBase-view (suc d) (suc o)  = Others (m≤n+m (suc o) (suc d))

--------------------------------------------------------------------------------
-- next-number
--------------------------------------------------------------------------------

next-number-NullBase : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → ¬ (Maximum xs)
    → Num 0 (suc d) o
next-number-NullBase {d} {o} xs ¬max with NullBase-view d o
next-number-NullBase xs       ¬max | AllZeros = contradiction (Maximum-AllZeros xs) ¬max
next-number-NullBase xs       ¬max | Others bound with Greatest? (lsd xs)
next-number-NullBase xs       ¬max | Others bound | yes greatest = contradiction (Maximum-NullBase-Greatest xs greatest) ¬max
next-number-NullBase (x ∙   ) ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∙
next-number-NullBase (x ∷ xs) ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∷ xs

mutual
    Gapped : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Set
    Gapped {b} {d} {o} (x ∙)    _     = suc d < (1 ⊔ o)                * suc b
    Gapped {b} {d} {o} (x ∷ xs) d+o≥2 = suc d < (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
        where
            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Proper xs d+o≥2

    Gapped? : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Dec (Gapped {b} {d} {o} xs d+o≥2)
    Gapped? {b} {d} {o} (x ∙)    _     = suc (suc d) ≤? (1 ⊔ o)                * suc b
    Gapped? {b} {d} {o} (x ∷ xs) d+o≥2 = suc (suc d) ≤? (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
        where
            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Proper xs d+o≥2

    data NextView : (b d o : ℕ) (xs : Num b d o) (d+o≥2 : 2 ≤ d + o) → Set where
        NeedNoCarry : ∀ b d o
            → {xs : Num (suc b) (suc d) o}
            → {d+o≥2 : 2 ≤ suc (d + o)}
            → (¬greatest : ¬ (Greatest (lsd xs)))
            → NextView (suc b) (suc d) o xs d+o≥2
        IsGapped : ∀ b d o
            → {xs : Num (suc b) (suc d) o}
            → {d+o≥2 : 2 ≤ suc (d + o)}
            → (greatest : Greatest (lsd xs))
            → (gapped : Gapped xs d+o≥2)
            → NextView (suc b) (suc d) o xs d+o≥2
        NotGapped : ∀ b d o
            → {xs : Num (suc b) (suc d) o}
            → {d+o≥2 : 2 ≤ suc (d + o)}
            → (greatest : Greatest (lsd xs))
            → (¬gapped : ¬ (Gapped xs d+o≥2))
            → NextView (suc b) (suc d) o xs d+o≥2

    nextView : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → NextView (suc b) (suc d) o xs d+o≥2
    nextView {b} {d} {o} xs d+o≥2 with Greatest? (lsd xs)
    nextView {b} {d} {o} xs d+o≥2 | yes greatest with Gapped? xs d+o≥2
    nextView {b} {d} {o} xs d+o≥2 | yes greatest | yes gapped = IsGapped b d o greatest gapped
    nextView {b} {d} {o} xs d+o≥2 | yes greatest | no ¬gapped = NotGapped b d o greatest ¬gapped
    nextView {b} {d} {o} xs d+o≥2 | no ¬greatest = NeedNoCarry b d o ¬greatest

    next-number-Proper-NeedNoCarry : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (¬greatest : ¬ (Greatest (lsd xs)))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Num (suc b) (suc d) o
    next-number-Proper-NeedNoCarry (x ∙)    ¬greatest d+o≥2 = digit+1 x ¬greatest ∙
    next-number-Proper-NeedNoCarry (x ∷ xs) ¬greatest d+o≥2 = digit+1 x ¬greatest ∷ xs

    next-number-Proper-IsGapped : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → (gapped : Gapped xs d+o≥2)
        → Num (suc b) (suc d) o
    next-number-Proper-IsGapped {b} {d} {o} (x ∙)    d+o≥2 gapped = z ∷ LCD d o d+o≥2 ∙
    next-number-Proper-IsGapped {b} {d} {o} (x ∷ xs) d+o≥2 gapped = z ∷ next-number-Proper xs d+o≥2

    next-number-Proper-NotGapped : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (greatest : Greatest (lsd xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → (¬gapped : ¬ (Gapped xs d+o≥2))
        → Num (suc b) (suc d) o
    next-number-Proper-NotGapped {b} {d} {o} (x ∙)    greatest d+o≥2 gapped
        = digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ LCD d o d+o≥2 ∙
        where
            lower-bound : (1 ⊔ o) * suc b > 0
            lower-bound =
                start
                    1
                ≈⟨ refl ⟩
                    1 * 1
                ≤⟨ m≤m⊔n 1 o *-mono s≤s z≤n ⟩
                    (1 ⊔ o) * suc b
                □
    next-number-Proper-NotGapped {b} {d} {o} (x ∷ xs) greatest d+o≥2 gapped
        = digit+1-n x greatest gap lower-bound ∷ next-xs
        where
            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Proper xs d+o≥2

            gap : ℕ
            gap = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b

            lower-bound : gap > 0
            lower-bound =
                start
                    1
                ≈⟨ refl ⟩
                    1 * 1
                ≤⟨ n*-mono 1 (s≤s {zero} {b} z≤n) ⟩
                    1 * suc b
                ≤⟨ *n-mono (suc b) (m≥n+o⇒m∸o≥n ⟦ next-xs ⟧ 1 ⟦ xs ⟧ (next-number-is-greater-Proper xs d+o≥2)) ⟩
                    (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
                □


    next-number-Proper : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Num (suc b) (suc d) o
    next-number-Proper xs d+o≥2 with nextView xs d+o≥2
    next-number-Proper xs d+o≥2 | NeedNoCarry b d o ¬greatest
        = next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2
    next-number-Proper xs d+o≥2 | IsGapped b d o greatest gapped
        = next-number-Proper-IsGapped xs d+o≥2 gapped
    next-number-Proper xs d+o≥2 | NotGapped b d o greatest ¬gapped
        = next-number-Proper-NotGapped xs greatest d+o≥2 ¬gapped

    next-number-is-greater-Proper : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → ⟦ next-number-Proper xs d+o≥2 ⟧ > ⟦ xs ⟧
    next-number-is-greater-Proper xs d+o≥2 with nextView xs d+o≥2
    next-number-is-greater-Proper (x ∙) d+o≥2 | NeedNoCarry b d o ¬greatest
        = reflexive $ sym (Digit-toℕ-digit+1 x ¬greatest)
    next-number-is-greater-Proper (x ∷ xs) d+o≥2 | NeedNoCarry b d o ¬greatest
        = reflexive $ cong (λ w → w + ⟦ xs ⟧ * suc b) (sym (Digit-toℕ-digit+1 x ¬greatest))
    next-number-is-greater-Proper (x ∙) d+o≥2 | IsGapped b d o greatest gapped =
        start
            suc (Fin.toℕ x + o)
        ≈⟨ cong (λ w → w + o) greatest ⟩
            suc d + o
        ≈⟨ +-comm (suc d) o ⟩
            o + suc d
        ≤⟨ n+-mono o (<⇒≤ gapped) ⟩
            o + (suc zero ⊔ o) * suc b
        ≈⟨ cong (λ w → o + w * suc b) (sym (LCD-toℕ d o d+o≥2)) ⟩
            o + (Digit-toℕ (LCD d o d+o≥2) o) * suc b
        □
    next-number-is-greater-Proper (x ∷ xs) d+o≥2 | IsGapped b d o greatest gapped =
        start
            suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
        ≈⟨ cong (λ w → suc w + ⟦ xs ⟧ * suc b) (toℕ-greatest x greatest) ⟩
            suc d + o + ⟦ xs ⟧ * suc b
        ≈⟨ +-assoc (suc d) o (⟦ xs ⟧ * suc b) ⟩
            suc d + (o + ⟦ xs ⟧ * suc b)
        ≈⟨ a+[b+c]≡b+[a+c] (suc d) o (⟦ xs ⟧ * suc b) ⟩
            o + (suc d + ⟦ xs ⟧ * suc b)
        ≤⟨ n+-mono o (+n-mono (⟦ xs ⟧ * suc b) (<⇒≤ gapped)) ⟩
            o + ((⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b + ⟦ xs ⟧ * suc b)
        ≈⟨ cong (λ w → o + w) (sym (distribʳ-*-+ (suc b) (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) ⟦ xs ⟧)) ⟩
            o + (⟦ next-xs ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧) * suc b
        ≈⟨ cong (λ w → o + w * suc b) (m∸n+n≡m (<⇒≤ next-xs>xs)) ⟩
            o + ⟦ next-xs ⟧ * suc b
        ≈⟨ refl ⟩
            ⟦ z ∷ next-xs ⟧
        □
        where
            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Proper xs d+o≥2

            next-xs>xs : ⟦ next-xs ⟧ > ⟦ xs ⟧
            next-xs>xs = next-number-is-greater-Proper xs d+o≥2

    next-number-is-greater-Proper (x ∙) d+o≥2 | NotGapped b d o greatest ¬gapped =
        start
            suc (Fin.toℕ x + o)
        ≈⟨ sym (m∸n+n≡m {_} {(suc zero ⊔ o) * suc b} upper-bound') ⟩
            suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + (suc zero ⊔ o) * suc b
        ≈⟨ cong (λ w → suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + w * suc b) (sym (LCD-toℕ d o d+o≥2)) ⟩
            suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + (Digit-toℕ (LCD d o d+o≥2) o) * suc b
        ≈⟨ cong (λ w → w + (Digit-toℕ (LCD d o d+o≥2) o) * suc b) (sym (Digit-toℕ-digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound upper-bound)) ⟩
            Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + (Digit-toℕ (LCD d o d+o≥2) o) * suc b
        □
        where
            upper-bound : (suc zero ⊔ o) * suc b ≤ suc d
            upper-bound = ≤-pred (≰⇒> ¬gapped)

            lower-bound : 1 ≤ (suc zero ⊔ o) * suc b
            lower-bound = start
                    1
                ≈⟨ refl ⟩
                    1 * 1
                ≤⟨ m≤m⊔n 1 o *-mono s≤s z≤n ⟩
                    (1 ⊔ o) * suc b
                □

            upper-bound' : (suc zero ⊔ o) * suc b ≤ suc (Digit-toℕ x o)
            upper-bound' =
                start
                    (suc zero ⊔ o) * suc b
                ≤⟨ upper-bound ⟩
                    suc d
                ≈⟨ sym greatest ⟩
                    suc (Fin.toℕ x)
                ≤⟨ m≤m+n (suc (Fin.toℕ x)) o ⟩
                    suc (Fin.toℕ x + o)
                □
    next-number-is-greater-Proper (x ∷ xs) d+o≥2 | NotGapped b d o greatest ¬gapped =
        start
            suc ⟦ x ∷ xs ⟧
        ≈⟨ sym (m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ xs ⟧ * suc b) (⟦ next-xs ⟧ * suc b) (*n-mono (suc b) (<⇒≤ ⟦next-xs⟧>⟦xs⟧)) upper-bound') ⟩
            suc (Digit-toℕ x o) ∸ (⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b) + ⟦ next-xs ⟧ * suc b
        ≈⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + ⟦ next-xs ⟧ * suc b) (sym (*-distrib-∸ʳ (suc b) ⟦ next-xs ⟧ ⟦ xs ⟧)) ⟩
            suc (Digit-toℕ x o) ∸ (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b + ⟦ next-xs ⟧ * suc b
        ≈⟨ cong (λ w → w + ⟦ next-xs ⟧ * suc b) (sym (Digit-toℕ-digit+1-n x greatest gap lower-bound upper-bound)) ⟩
            Digit-toℕ next-x o + ⟦ next-xs ⟧ * suc b
        □
        where
            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Proper xs d+o≥2

            gap : ℕ
            gap = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b

            lower-bound : gap > 0
            lower-bound =
                start
                    1
                ≈⟨ refl ⟩
                    1 * 1
                ≤⟨ n*-mono 1 (s≤s {zero} {b} z≤n) ⟩
                    1 * suc b
                ≤⟨ *n-mono (suc b) (m≥n+o⇒m∸o≥n ⟦ next-xs ⟧ 1 ⟦ xs ⟧ (next-number-is-greater-Proper xs d+o≥2)) ⟩
                    (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
                □

            upper-bound : gap ≤ suc d
            upper-bound = ≤-pred (≰⇒> ¬gapped)

            next-x : Digit (suc d)
            next-x = digit+1-n x greatest gap lower-bound

            next : Num (suc b) (suc d) o
            next = digit+1-n x greatest gap lower-bound ∷ next-xs

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

gap : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ℕ
gap {b} {d} {o} (x ∙)    d+o≥2 = (1 ⊔ o)                * suc b
gap {b} {d} {o} (x ∷ xs) d+o≥2 = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
    where
        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Proper xs d+o≥2

gap>0 : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → gap xs d+o≥2 > 0
gap>0 {b} {d} {o} (x ∙)    d+o≥2 =
    start
        1
    ≈⟨ refl ⟩
        1 * 1
    ≤⟨ m≤m⊔n 1 o *-mono s≤s z≤n ⟩
        (1 ⊔ o) * suc b
    □
gap>0 {b} {d} {o} (x ∷ xs) d+o≥2 =
    start
        1
    ≈⟨ refl ⟩
        1 * 1
    ≤⟨ n*-mono 1 (s≤s {zero} {b} z≤n) ⟩
        1 * suc b
    ≤⟨ *n-mono (suc b) (m≥n+o⇒m∸o≥n ⟦ next-xs ⟧ 1 ⟦ xs ⟧ (next-number-is-greater-Proper xs d+o≥2)) ⟩
        (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
    □
    where
        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Proper xs d+o≥2

next-number : ∀ {b d o}
    → (xs : Num b d o)
    → ¬ (Maximum xs)
    → Num b d o
next-number {b} {d} {o} xs ¬max with numView b d o
next-number xs ¬max | NullBase d o = next-number-NullBase xs ¬max
next-number xs ¬max | NoDigits b o = NoDigits-explode xs
next-number xs ¬max | AllZeros b = contradiction (Maximum-AllZeros xs) ¬max
next-number xs ¬max | Proper b d o d+o≥2 = next-number-Proper xs d+o≥2

--------------------------------------------------------------------------------
-- next-number-is-greater
--------------------------------------------------------------------------------

next-number-is-greater-NullBase : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ next-number-NullBase xs ¬max ⟧ > ⟦ xs ⟧
next-number-is-greater-NullBase {d} {o} xs    ¬max with NullBase-view d o
next-number-is-greater-NullBase xs        ¬max | AllZeros = contradiction (Maximum-AllZeros xs) ¬max
next-number-is-greater-NullBase xs        ¬max | Others bound with Greatest? (lsd xs)
next-number-is-greater-NullBase xs        ¬max | Others bound | yes greatest = contradiction (Maximum-NullBase-Greatest xs greatest) ¬max
next-number-is-greater-NullBase (x ∙)     ¬max | Others bound | no ¬greatest = reflexive (sym (Digit-toℕ-digit+1 x ¬greatest))
next-number-is-greater-NullBase (x ∷ xs)  ¬max | Others bound | no ¬greatest = +n-mono (⟦ xs ⟧ * 0) (reflexive (sym (Digit-toℕ-digit+1 x ¬greatest)))

next-number-is-greater : ∀ {b d o}
    → (xs : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ next-number xs ¬max ⟧ > ⟦ xs ⟧
next-number-is-greater {b} {d} {o} xs ¬max with numView b d o
next-number-is-greater xs ¬max | NullBase d o = next-number-is-greater-NullBase xs ¬max
next-number-is-greater xs ¬max | NoDigits b o = NoDigits-explode xs
next-number-is-greater xs ¬max | AllZeros b = contradiction (Maximum-AllZeros xs) ¬max
next-number-is-greater xs ¬max | Proper b d o d+o≥2 = next-number-is-greater-Proper xs d+o≥2

--------------------------------------------------------------------------------
-- Properties of next-number on Proper Numbers
--------------------------------------------------------------------------------

next-number-Proper-refine-target : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → NextView (suc b) (suc d) o xs d+o≥2
    → Set
next-number-Proper-refine-target xs d+o≥2 (NeedNoCarry b d o ¬greatest) = next-number-Proper xs d+o≥2 ≡ next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2
next-number-Proper-refine-target xs d+o≥2 (IsGapped b d o greatest gapped) = next-number-Proper xs d+o≥2 ≡ next-number-Proper-IsGapped xs d+o≥2 gapped
next-number-Proper-refine-target xs d+o≥2 (NotGapped b d o greatest ¬gapped) = next-number-Proper xs d+o≥2 ≡ next-number-Proper-NotGapped xs greatest d+o≥2 ¬gapped

next-number-Proper-refine : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (view : NextView (suc b) (suc d) o xs d+o≥2)
    → next-number-Proper-refine-target xs d+o≥2 view
next-number-Proper-refine xs d+o≥2 (NeedNoCarry b d o ¬greatest) with nextView xs d+o≥2
next-number-Proper-refine xs d+o≥2 (NeedNoCarry b d o ¬greatest) | NeedNoCarry _ _ _ _ = refl
next-number-Proper-refine xs d+o≥2 (NeedNoCarry b d o ¬greatest) | IsGapped _ _ _ greatest _ = contradiction greatest ¬greatest
next-number-Proper-refine xs d+o≥2 (NeedNoCarry b d o ¬greatest) | NotGapped _ _ _ greatest _ = contradiction greatest ¬greatest
next-number-Proper-refine xs d+o≥2 (IsGapped b d o greatest gapped) with nextView xs d+o≥2
next-number-Proper-refine xs d+o≥2 (IsGapped b d o greatest gapped) | NeedNoCarry _ _ _ ¬greatest = contradiction greatest ¬greatest
next-number-Proper-refine xs d+o≥2 (IsGapped b d o greatest gapped) | IsGapped _ _ _ _ _ = refl
next-number-Proper-refine xs d+o≥2 (IsGapped b d o greatest gapped) | NotGapped _ _ _ _ ¬gapped = contradiction gapped ¬gapped
next-number-Proper-refine xs d+o≥2 (NotGapped b d o greatest ¬gapped) with nextView xs d+o≥2
next-number-Proper-refine xs d+o≥2 (NotGapped b d o greatest ¬gapped) | NeedNoCarry _ _ _ ¬greatest = contradiction greatest ¬greatest
next-number-Proper-refine xs d+o≥2 (NotGapped b d o greatest ¬gapped) | IsGapped _ _ _ _ gapped = contradiction gapped ¬gapped
next-number-Proper-refine xs d+o≥2 (NotGapped b d o greatest ¬gapped) | NotGapped _ _ _ _ _ = refl


next-number-Proper-NeedNoCarry-lemma : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (¬greatest : ¬ (Greatest (lsd xs)))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ⟦ next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2 ⟧ ≡ suc ⟦ xs ⟧
next-number-Proper-NeedNoCarry-lemma {b} {d} {o} (x ∙) ¬greatest d+o≥2 =
    -- ⟦ digit+1 x ¬greatest ∙ ⟧ ≡ suc ⟦ x ∙ ⟧
    begin
        Digit-toℕ (digit+1 x ¬greatest) o
    ≡⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Digit-toℕ x o)
    ∎
next-number-Proper-NeedNoCarry-lemma {b} {d} {o} (x ∷ xs) ¬greatest d+o≥2 =
-- ⟦ digit+1 x ¬greatest ∷ xs ⟧ ≡ suc ⟦ x ∷ xs ⟧
    begin
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * suc b
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
    ∎

next-number-Proper-IsGapped-lemma : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (greatest : Greatest (lsd xs))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (gapped : Gapped xs d+o≥2)
    → ⟦ next-number-Proper-IsGapped xs d+o≥2 gapped ⟧ > suc ⟦ xs ⟧
next-number-Proper-IsGapped-lemma {b} {d} {o} (x ∙) greatest d+o≥2 gapped =
    -- ⟦ z ∷ LCD d o d+o≥2 ∙ ⟧ > suc ⟦ x ∙ ⟧
    start
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
next-number-Proper-IsGapped-lemma {b} {d} {o} (x ∷ xs) greatest d+o≥2 gapped
    = proof
    where
        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Proper xs d+o≥2

        next-xs>xs : ⟦ next-xs ⟧ > ⟦ xs ⟧
        next-xs>xs = next-number-is-greater-Proper xs d+o≥2

        next : Num (suc b) (suc d) o
        next = z ∷ next-xs

        -- ⟦ z ∷ next-number-Proper xs (Maximum-Proper xs d+o≥2) d+o≥2 ⟧ > suc ⟦ x ∷ xs ⟧
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

next-number-Proper-NotGapped-lemma : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (greatest : Greatest (lsd xs))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → (¬gapped : ¬ (Gapped xs d+o≥2))
    → ⟦ next-number-Proper-NotGapped xs greatest d+o≥2 ¬gapped ⟧ ≡ suc ⟦ xs ⟧
next-number-Proper-NotGapped-lemma {b} {d} {o} (x ∙)    greatest d+o≥2 ¬gapped = proof
    -- ⟦ digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ LCD d o d+o≥2 ∙ ⟧ ≡ suc ⟦ x ∙ ⟧
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
next-number-Proper-NotGapped-lemma {b} {d} {o} (x ∷ xs) greatest d+o≥2 ¬gapped = proof
    -- ⟦ digit+1-n x greatest gap gap>0 ∷ next ∙ ⟧ ≡ suc ⟦ x ∷ xs ⟧
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

--------------------------------------------------------------------------------
-- next-number-is-LUB
--------------------------------------------------------------------------------

next-number-is-LUB-NullBase : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (ys : Num 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ ys ⟧ > ⟦ xs ⟧
    → ⟦ ys ⟧ ≥ ⟦ next-number-NullBase xs ¬max ⟧
next-number-is-LUB-NullBase {d} {o} xs ys ¬max prop with NullBase-view d o
next-number-is-LUB-NullBase {_} {_} xs ys ¬max prop | AllZeros = contradiction (Maximum-AllZeros xs) ¬max
next-number-is-LUB-NullBase {d} {o} xs ys ¬max prop | Others bound with Greatest? (lsd xs)
next-number-is-LUB-NullBase {d} {o} xs ys ¬max prop | Others bound | yes greatest = contradiction (Maximum-NullBase-Greatest xs greatest) ¬max
next-number-is-LUB-NullBase {d} {o} (x ∙) ys ¬max prop | Others bound | no ¬greatest =
    start
        Digit-toℕ (digit+1 x ¬greatest) o
    ≈⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Digit-toℕ x o)
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □
next-number-is-LUB-NullBase {d} {o} (x ∷ xs) ys ¬max prop | Others bound | no ¬greatest =
    start
        ⟦ digit+1 x ¬greatest ∷ xs ⟧
    ≈⟨ cong (λ w → w + ⟦ xs ⟧ * 0) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Digit-toℕ x o) + ⟦ xs ⟧ * 0
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □


next-number-is-LUB-Proper : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (ys : Num (suc b) (suc d) o)
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ⟦ ys ⟧ > ⟦ xs ⟧
    → ⟦ ys ⟧ ≥ ⟦ next-number-Proper xs d+o≥2 ⟧
next-number-is-LUB-Proper xs ys d+o≥2 prop with nextView xs d+o≥2
next-number-is-LUB-Proper xs ys d+o≥2 prop | NeedNoCarry b d o ¬greatest =
    start
        ⟦ next-number-Proper-NeedNoCarry xs ¬greatest d+o≥2 ⟧
    ≈⟨ next-number-Proper-NeedNoCarry-lemma xs ¬greatest d+o≥2 ⟩
        suc ⟦ xs ⟧
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □
next-number-is-LUB-Proper xs (y ∙) d+o≥2 prop | IsGapped b d o greatest gapped
    = contradiction prop $ >⇒≰ $
        start
            suc (Digit-toℕ y o)
        ≤⟨ s≤s (greatest-of-all o (lsd xs) y greatest) ⟩
            suc (Digit-toℕ (lsd xs) o)
        ≤⟨ s≤s (lsd-toℕ xs) ⟩
            suc ⟦ xs ⟧
        □
next-number-is-LUB-Proper (x ∙) (y ∷ ys) d+o≥2 prop | IsGapped b d o greatest gapped =
    let
        ⟦ys⟧>0 = tail-mono-strict-Null x y ys greatest prop
    in
    start
        o + (Digit-toℕ (LCD d o d+o≥2) o) * suc b
    ≈⟨ cong (λ w → o + w * suc b) (LCD-toℕ d o d+o≥2) ⟩
        o + (1 ⊔ o) * suc b
    ≤⟨ n+-mono o (*n-mono (suc b) ys-lower-bound) ⟩
        o + ⟦ ys ⟧ * suc b
    ≤⟨ +n-mono (⟦ ys ⟧ * suc b) (m≤n+m o (Fin.toℕ y)) ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □
    where
        ≥1⊔o : ∀ {b d o}
            → (xs : Num (suc b) (suc d) o)
            → (d+o≥2 : 2 ≤ suc (d + o))
            → ⟦ xs ⟧ ≥ 1
            → ⟦ xs ⟧ ≥ 1 ⊔ o
        ≥1⊔o {_} {_} {zero}  xs d+o≥2 prop = prop
        ≥1⊔o {_} {_} {suc o} (x ∙) d+o≥2 prop = m≤n+m (suc o) (Fin.toℕ x)
        ≥1⊔o {b} {_} {suc o} (x ∷ xs) d+o≥2 prop =
            start
                suc o
            ≤⟨ m≤n+m (suc o) (Fin.toℕ x) ⟩
                Fin.toℕ x + suc o
            ≤⟨ m≤m+n (Fin.toℕ x + suc o) (⟦ xs ⟧ * suc b) ⟩
                Fin.toℕ x + suc o + ⟦ xs ⟧ * suc b
            □

        ys-lower-bound : ⟦ ys ⟧ ≥ 1 ⊔ o
        ys-lower-bound = ≥1⊔o ys d+o≥2 (tail-mono-strict-Null x y ys greatest prop)

next-number-is-LUB-Proper (x ∷ xs) (y ∷ ys) d+o≥2 prop | IsGapped b d o greatest gapped =
    start
        o + ⟦ next-xs ⟧ * suc b
    ≤⟨ n+-mono o (*n-mono (suc b) ⟦next-xs⟧≤⟦ys⟧) ⟩
        o + ⟦ ys ⟧ * suc b
    ≤⟨ +n-mono (⟦ ys ⟧ * suc b) (m≤n+m o (Fin.toℕ y)) ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □
    where
        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = Maximum-Proper xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Proper xs d+o≥2

        ⟦xs⟧<⟦ys⟧ : ⟦ xs ⟧ < ⟦ ys ⟧
        ⟦xs⟧<⟦ys⟧ = tail-mono-strict x xs y ys greatest prop

        ⟦next-xs⟧≤⟦ys⟧ : ⟦ next-xs ⟧ ≤ ⟦ ys ⟧
        ⟦next-xs⟧≤⟦ys⟧ = next-number-is-LUB-Proper xs ys d+o≥2 ⟦xs⟧<⟦ys⟧

next-number-is-LUB-Proper xs ys d+o≥2 prop | NotGapped b d o greatest ¬gapped =
    start
        ⟦ next-number-Proper-NotGapped xs greatest d+o≥2 ¬gapped ⟧
    ≈⟨ next-number-Proper-NotGapped-lemma xs greatest d+o≥2 ¬gapped ⟩
        suc ⟦ xs ⟧
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □

next-number-is-LUB : ∀ {b d o}
    → (xs : Num b d o)
    → (ys : Num b d o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ ys ⟧ > ⟦ xs ⟧
    → ⟦ ys ⟧ ≥ ⟦ next-number xs ¬max ⟧
next-number-is-LUB {b} {d} {o} xs ys ¬max prop with numView b d o
next-number-is-LUB xs ys ¬max prop | NullBase d o = next-number-is-LUB-NullBase xs ys ¬max prop
next-number-is-LUB xs ys ¬max prop | NoDigits b o = NoDigits-explode xs
next-number-is-LUB xs ys ¬max prop | AllZeros b = contradiction (Maximum-AllZeros xs) ¬max
next-number-is-LUB xs ys ¬max prop | Proper b d o d+o≥2 = next-number-is-LUB-Proper xs ys d+o≥2 prop
