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
    Others : ∀ {d o} → (bound : d + o ≥ 1 ⊔ o) → NullBase-View d o

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


next-number-1⊔o-upper-bound : ∀ m n → 2 ≤ suc m + n → m + n ≥ 1 ⊔ n
next-number-1⊔o-upper-bound m zero    q = ≤-pred q
next-number-1⊔o-upper-bound m (suc n) q = m≤n+m (suc n) m

mutual

    data Others-View-Single : (b d o : ℕ) (x : Digit d) → Set where
        NeedNoCarry : ∀ {b d o}
            → {x : Digit (suc d)}
            → (¬greatest : ¬ (Greatest x))
            → Others-View-Single (suc b) (suc d) o x
        Gapped : ∀ {b d o}
            → {x : Digit (suc d)}
            → (greatest : Greatest x)
            → (gapped : suc d < (1 ⊔ o) * suc b)
            → Others-View-Single (suc b) (suc d) o x
        ¬Gapped : ∀ {b d o}
            → {x : Digit (suc d)}
            → (greatest : Greatest x)
            → (¬gapped : suc d ≥ (1 ⊔ o) * suc b)
            → Others-View-Single (suc b) (suc d) o x

    data Others-View : (b d o : ℕ) (x : Digit d) (xs : Num b d o) (d+o≥2 : 2 ≤ d + o) → Set where
        NeedNoCarry : ∀ {b d o}
            → {x : Digit (suc d)}
            → {xs : Num (suc b) (suc d) o}
            → {d+o≥2 : 2 ≤ suc (d + o)}
            → (¬greatest : ¬ (Greatest x))
            → Others-View (suc b) (suc d) o x xs d+o≥2
        Gapped : ∀ {b d o}
            → {x : Digit (suc d)}
            → {xs : Num (suc b) (suc d) o}
            → {d+o≥2 : 2 ≤ suc (d + o)}
            → (greatest : Greatest x)
            →   let ¬max = Maximum-Others xs d+o≥2
                    next = next-number-Others xs ¬max d+o≥2
                in  (gapped : suc d < (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b)
            → Others-View (suc b) (suc d) o x xs d+o≥2
        ¬Gapped : ∀ {b d o}
            → {x : Digit (suc d)}
            → {xs : Num (suc b) (suc d) o}
            → {d+o≥2 : 2 ≤ suc (d + o)}
            → (greatest : Greatest x)
            →   let ¬max = Maximum-Others xs d+o≥2
                    next = next-number-Others xs ¬max d+o≥2
                in  (¬gapped : suc d ≥ (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b)
            → Others-View (suc b) (suc d) o x xs d+o≥2

    Others-view-single : ∀ b d o
        → (x : Digit (suc d))
        → Others-View-Single (suc b) (suc d) o x
    Others-view-single b d o x with Greatest? x
    Others-view-single b d o x | yes greatest with suc (suc d) ≤? (1 ⊔ o) * suc b
    Others-view-single b d o x | yes greatest | yes gapped = Gapped greatest gapped
    Others-view-single b d o x | yes greatest | no ¬gapped = ¬Gapped greatest (≤-pred $ ≰⇒> ¬gapped)
    Others-view-single b d o x | no ¬greatest = NeedNoCarry ¬greatest

    Others-view : ∀ {b d o}
        → (x : Digit (suc d))
        → (xs : Num (suc b) (suc d) o)
        → ¬ (Maximum (x ∷ xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Others-View (suc b) (suc d) o x xs d+o≥2
    Others-view {b} {d} {o} x xs ¬max d+o≥2 with Greatest? x
    Others-view {b} {d} {o} x xs ¬max d+o≥2 | yes greatest with suc (suc d) ≤? (⟦ next-number-Others xs (Maximum-Others xs d+o≥2) d+o≥2 ⟧ ∸ ⟦ xs ⟧) * suc b
    Others-view {b} {d} {o} x xs ¬max d+o≥2 | yes greatest | yes gapped = Gapped greatest gapped
    Others-view {b} {d} {o} x xs ¬max d+o≥2 | yes greatest | no ¬gapped = ¬Gapped greatest (≤-pred $ ≰⇒> ¬gapped)
    Others-view {b} {d} {o} x xs ¬max d+o≥2 | no ¬greatest = NeedNoCarry ¬greatest


    -- 1 `max` o, in case that the least digit "o" is 0, which is too small
    1⊔o : ∀ d o → 2 ≤ suc (d + o) → Digit (suc d)
    1⊔o d o d+o≥2 = Digit-fromℕ (1 ⊔ o) o (next-number-1⊔o-upper-bound d o d+o≥2)

    next-number-Others : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → ¬ (Maximum xs)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Num (suc b) (suc d) o
    next-number-Others {b} {d} {o} (x ∙) ¬max d+o≥2 with Others-view-single b d o x
    next-number-Others {b} {d} {o} (x ∙) ¬max d+o≥2 | NeedNoCarry ¬greatest
        = digit+1 x ¬greatest ∙
    next-number-Others {b} {d} {o} (x ∙) ¬max d+o≥2 | Gapped greatest gapped
        = z ∷ 1⊔o d o d+o≥2 ∙
    next-number-Others {b} {d} {o} (x ∙) ¬max d+o≥2 | ¬Gapped greatest ¬gapped =
        let lower-bound : (1 ⊔ o) * suc b > 0
            lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n
        in digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ 1⊔o d o d+o≥2 ∙
    next-number-Others {b} {d} {o} (x ∷ xs) ¬max d+o≥2 with Others-view x xs ¬max d+o≥2
    next-number-Others (x ∷ xs) ¬max d+o≥2 | NeedNoCarry ¬greatest
        = digit+1 x ¬greatest ∷ xs
    next-number-Others (x ∷ xs) ¬max d+o≥2 | Gapped greatest gapped =
        let
            ¬max = Maximum-Others xs d+o≥2
            next = next-number-Others xs ¬max d+o≥2
        in z ∷ next
    next-number-Others {b} {d} {o} (x ∷ xs) ¬max d+o≥2 | ¬Gapped greatest ¬gapped =
        let
            ¬max = Maximum-Others xs d+o≥2
            next = next-number-Others xs ¬max d+o≥2
            gap = (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b
            gap>0 = (start
                    1
                ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ xs ⟧))) ⟩
                    suc (⟦ xs ⟧ ∸ ⟦ xs ⟧)
                ≈⟨ sym (+-∸-assoc 1 {⟦ xs ⟧} ≤-refl) ⟩
                    suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
                ≤⟨ ∸-mono {suc ⟦ xs ⟧} {⟦ next ⟧} {⟦ xs ⟧} (next-number-is-greater-Others xs ¬max d+o≥2) ≤-refl ⟩
                    ⟦ next ⟧ ∸ ⟦ xs ⟧
                □) *-mono (s≤s {0} {b} z≤n)
        in digit+1-n x greatest gap gap>0 ∷ next

    -- properties of the actual function
    Digit-toℕ-1⊔o : ∀ d o
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Digit-toℕ (1⊔o d o d+o≥2) o ≡ 1 ⊔ o
    Digit-toℕ-1⊔o d o d+o≥2 = Digit-toℕ-fromℕ {d} {o} (1 ⊔ o) upper-bound lower-bound
        where
            lower-bound : o ≤ 1 ⊔ o
            lower-bound =
                start
                    o
                ≤⟨ m≤m⊔n o (suc zero) ⟩
                    o ⊔ suc zero
                ≈⟨ ⊔-comm o (suc zero) ⟩
                    suc zero ⊔ o
                □
            upper-bound : d + o ≥ 1 ⊔ o
            upper-bound = next-number-1⊔o-upper-bound d o d+o≥2

    next-number-is-greater-Others : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (¬max : ¬ (Maximum xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → ⟦ next-number-Others xs ¬max d+o≥2 ⟧ > ⟦ xs ⟧
    next-number-is-greater-Others {b} {d} {o} (x ∙) ¬max d+o≥2 with Others-view-single b d o x
    next-number-is-greater-Others {b} {d} {o} (x ∙) ¬max d+o≥2 | NeedNoCarry ¬greatest
        = reflexive $ sym (Digit-toℕ-digit+1 x ¬greatest)
    next-number-is-greater-Others {b} {d} {o} (x ∙) ¬max d+o≥2 | Gapped greatest gapped =
        start
            suc (Fin.toℕ x + o)
        ≈⟨ cong (λ w → w + o) greatest ⟩
            suc d + o
        ≈⟨ +-comm (suc d) o ⟩
            o + suc d
        ≤⟨ n+-mono o (<⇒≤ gapped) ⟩
            o + (suc zero ⊔ o) * suc b
        ≈⟨ cong (λ w → o + w * suc b) (sym (Digit-toℕ-1⊔o d o d+o≥2)) ⟩
            o + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
        □
    next-number-is-greater-Others {b} {d} {o} (x ∙) ¬max d+o≥2 | ¬Gapped greatest ¬gapped =
        let
            lower-bound : (suc zero ⊔ o) * suc b ≤ suc d
            lower-bound = ¬gapped
            upper-bound : 1 ≤ (suc zero ⊔ o) * suc b
            upper-bound = m≤m⊔n (suc zero) o *-mono s≤s z≤n
            upper-bound' : (suc zero ⊔ o) * suc b ≤ suc (Digit-toℕ x o)
            upper-bound' =
                start
                    (suc zero ⊔ o) * suc b
                ≤⟨ lower-bound ⟩
                    suc d
                ≈⟨ sym greatest ⟩
                    suc (Fin.toℕ x)
                ≤⟨ m≤m+n (suc (Fin.toℕ x)) o ⟩
                    suc (Fin.toℕ x + o)
                □
        in start
            suc (Fin.toℕ x + o)
        ≈⟨ sym (m∸n+n≡m {_} {(suc zero ⊔ o) * suc b} upper-bound') ⟩
            suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + (suc zero ⊔ o) * suc b
        ≈⟨ cong (λ w → suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + w * suc b) (sym (Digit-toℕ-1⊔o d o d+o≥2)) ⟩
            suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
        ≈⟨ cong (λ w → w + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b) (sym (Digit-toℕ-digit+1-n x greatest ((1 ⊔ o) * suc b) upper-bound lower-bound)) ⟩
            Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) upper-bound) o + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
        □
    next-number-is-greater-Others {b} {d} {o} (x ∷ xs) ¬max d+o≥2 with Others-view x xs ¬max d+o≥2
    next-number-is-greater-Others {b} {d} {o} (x ∷ xs) ¬max d+o≥2 | NeedNoCarry ¬greatest
        = reflexive $ cong (λ w → w + ⟦ xs ⟧ * suc b) (sym (Digit-toℕ-digit+1 x ¬greatest))
    next-number-is-greater-Others {b} {d} {o} (x ∷ xs) ¬max d+o≥2 | Gapped greatest gapped =
        let
            ¬max-xs : ¬ (Maximum xs)
            ¬max-xs = Maximum-Others xs d+o≥2
            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Others xs ¬max-xs d+o≥2
            next-xs>xs : ⟦ next-xs ⟧ > ⟦ xs ⟧
            next-xs>xs = next-number-is-greater-Others xs ¬max-xs d+o≥2
        in
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
    next-number-is-greater-Others {b} {d} {o} (x ∷ xs) ¬max d+o≥2 | ¬Gapped greatest ¬gapped =
        let
            ¬max = Maximum-Others xs d+o≥2
            next = next-number-Others xs ¬max d+o≥2
            gap = (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b
            gap>0 = (start
                    1
                ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ xs ⟧))) ⟩
                    suc (⟦ xs ⟧ ∸ ⟦ xs ⟧)
                ≈⟨ sym (+-∸-assoc 1 {⟦ xs ⟧} ≤-refl) ⟩
                    suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
                ≤⟨ ∸-mono {suc ⟦ xs ⟧} {⟦ next ⟧} {⟦ xs ⟧} (next-number-is-greater-Others xs ¬max d+o≥2) ≤-refl ⟩
                    ⟦ next ⟧ ∸ ⟦ xs ⟧
                □) *-mono (s≤s {0} {b} z≤n)
            gap<d = ¬gapped
            gap'-upper-bound =
                start
                    ⟦ next ⟧ * suc b ∸ ⟦ xs ⟧ * suc b
                ≈⟨ sym (*-distrib-∸ʳ (suc b) ⟦ next ⟧ ⟦ xs ⟧) ⟩
                    (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b
                ≤⟨ gap<d ⟩
                    suc d
                ≤⟨ m≤m+n (suc d) o ⟩
                    suc d + o
                ≈⟨ cong (λ w → w + o) (sym greatest) ⟩
                    suc (Digit-toℕ x o)
                □
            LSD = digit+1-n x greatest gap gap>0
            next>this = <⇒≤ $ next-number-is-greater-Others xs ¬max d+o≥2

        in start
            suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
        ≈⟨ sym (m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ xs ⟧ * suc b) (⟦ next ⟧ * suc b) (*n-mono (suc b) next>this) gap'-upper-bound) ⟩
            suc (Digit-toℕ x o) ∸ (⟦ next ⟧ * suc b ∸ ⟦ xs ⟧ * suc b) + ⟦ next ⟧ * suc b
        ≈⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + ⟦ next ⟧ * suc b) (sym (*-distrib-∸ʳ (suc b) ⟦ next ⟧ ⟦ xs ⟧)) ⟩
            suc (Digit-toℕ x o) ∸ (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b + ⟦ next ⟧ * suc b
        ≈⟨ cong (λ w → w + ⟦ next ⟧ * suc b) (sym (Digit-toℕ-digit+1-n x greatest gap gap>0 gap<d)) ⟩
            Digit-toℕ LSD o + ⟦ next ⟧ * suc b
        ≈⟨ refl ⟩
            ⟦ LSD ∷ next ⟧
        □

next-number : ∀ {b d o}
    → (xs : Num b d o)
    → ¬ (Maximum xs)
    → Num b d o
next-number {b} {d} {o} xs ¬max with numView b d o
next-number xs ¬max | NullBase d o = next-number-NullBase xs ¬max
next-number xs ¬max | NoDigits b o = NoDigits-explode xs
next-number xs ¬max | AllZeros b = contradiction (Maximum-AllZeros xs) ¬max
next-number xs ¬max | Others b d o d+o≥2 = next-number-Others xs ¬max d+o≥2

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
next-number-is-greater xs ¬max | Others b d o d+o≥2 = next-number-is-greater-Others xs ¬max d+o≥2


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

next-number-is-LUB-Others : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (ys : Num (suc b) (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ⟦ ys ⟧ > ⟦ xs ⟧
    → ⟦ ys ⟧ ≥ ⟦ next-number-Others xs ¬max d+o≥2 ⟧
next-number-is-LUB-Others {b} {d} {o} (x ∙) ys ¬max d+o≥2 prop with Others-view-single b d o x
next-number-is-LUB-Others {b} {d} {o} (x ∙) ys ¬max d+o≥2 prop | NeedNoCarry ¬greatest =
    start
        Digit-toℕ (digit+1 x ¬greatest) o
    ≈⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Digit-toℕ x o)
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □
next-number-is-LUB-Others {b} {d} {o} (x ∙) (y ∙) ¬max d+o≥2 prop | Gapped greatest gapped = contradiction prop (>⇒≰ (s≤s (greatest-of-all o x y greatest)))
next-number-is-LUB-Others {b} {d} {o} (x ∙) (y ∷ ys) ¬max d+o≥2 prop | Gapped greatest gapped =
    let
        ⟦ys⟧>0 = tail-mono-strict-Null x y ys greatest prop
    in
    start
        o + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
    ≈⟨ cong (λ w → o + w * suc b) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
        o + (1 ⊔ o) * suc b
    ≤⟨ n+-mono o (*n-mono (suc b) (≥1⊔o ys d+o≥2 ⟦ys⟧>0)) ⟩
        o + ⟦ ys ⟧ * suc b
    ≤⟨ +n-mono (⟦ ys ⟧ * suc b) (m≤n+m o (Fin.toℕ y)) ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □
next-number-is-LUB-Others {b} {d} {o} (x ∙) ys ¬max d+o≥2 prop | ¬Gapped greatest ¬gapped =
    let
        lower-bound : (1 ⊔ o) * suc b > 0
        lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n
        upper-bound : (1 ⊔ o) * suc b ≤ suc d
        upper-bound = ¬gapped
        upper-bound' : (1 ⊔ o) * suc b ≤ suc (Fin.toℕ x + o)
        upper-bound' = start
                (1 ⊔ o) * suc b
            ≤⟨ upper-bound ⟩
                suc d
            ≈⟨ sym greatest ⟩
                suc (Fin.toℕ x)
            ≤⟨ m≤m+n (suc (Fin.toℕ x)) o ⟩
                suc (Fin.toℕ x + o)
            □
    in
    start
        Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
    ≈⟨ cong (λ w → Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + w * suc b) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
        Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + (1 ⊔ o) * suc b
    ≈⟨ cong (λ w → w + (1 ⊔ o) * suc b) (Digit-toℕ-digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound upper-bound) ⟩
        suc (Fin.toℕ x + o) ∸ (1 ⊔ o) * suc b + (1 ⊔ o) * suc b
    ≈⟨ m∸n+n≡m upper-bound' ⟩
        suc (Fin.toℕ x + o)
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □
next-number-is-LUB-Others {b} {d} {o} (x ∷ xs) ys ¬max d+o≥2 prop with Others-view x xs ¬max d+o≥2
next-number-is-LUB-Others {b} {d} {o} (x ∷ xs) ys ¬max d+o≥2 prop | NeedNoCarry ¬greatest =
    start
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * suc b
    ≈⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □
next-number-is-LUB-Others {b} {d} {o} (x ∷ xs) (y ∙) ¬max d+o≥2 prop | Gapped greatest gapped = contradiction prop $ >⇒≰ $
    start
        suc (Fin.toℕ y + o)
    ≤⟨ s≤s (greatest-of-all o x y greatest) ⟩
        suc (Fin.toℕ x + o)
    ≤⟨ m≤m+n (suc (Fin.toℕ x + o)) (⟦ xs ⟧ * suc b) ⟩
        suc (Fin.toℕ x + o + ⟦ xs ⟧ * suc b)
    □
next-number-is-LUB-Others {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | Gapped greatest gapped =
    let
        ¬max = Maximum-Others xs d+o≥2
        next = next-number-Others xs ¬max d+o≥2
        ⟦y'∷ys⟧>⟦x'∷xs⟧ = tail-mono-strict x xs y ys greatest prop
    in
    start
        ⟦ z ∷ next ⟧
    ≤⟨ n+-mono o (*n-mono (suc b) (next-number-is-LUB-Others xs ys ¬max d+o≥2 ⟦y'∷ys⟧>⟦x'∷xs⟧)) ⟩
        o + ⟦ ys ⟧ * suc b
    ≤⟨ +n-mono (⟦ ys ⟧ * suc b) (m≤n+m o (Fin.toℕ y)) ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □
next-number-is-LUB-Others {b} {d} {o} (x ∷ xs) (y ∙) ¬max d+o≥2 prop | ¬Gapped greatest ¬gapped = contradiction prop $ >⇒≰ $
    start
        suc (Fin.toℕ y + o)
    ≤⟨ s≤s (greatest-of-all o x y greatest) ⟩
        suc (Fin.toℕ x + o)
    ≤⟨ m≤m+n (suc (Fin.toℕ x + o)) (⟦ xs ⟧ * suc b) ⟩
        suc (Fin.toℕ x + o + ⟦ xs ⟧ * suc b)
    □
next-number-is-LUB-Others {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | ¬Gapped greatest ¬gapped =
    let
        ¬max = Maximum-Others xs d+o≥2
        next = next-number-Others xs ¬max d+o≥2
        gap = (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b
        gap>0 = (start
                1
            ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ xs ⟧))) ⟩
                suc (⟦ xs ⟧ ∸ ⟦ xs ⟧)
            ≈⟨ sym (+-∸-assoc 1 {⟦ xs ⟧} ≤-refl) ⟩
                suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
            ≤⟨ ∸-mono {suc ⟦ xs ⟧} {⟦ next ⟧} {⟦ xs ⟧} (next-number-is-greater-Others xs ¬max d+o≥2) ≤-refl ⟩
                ⟦ next ⟧ ∸ ⟦ xs ⟧
            □) *-mono (s≤s {0} {b} z≤n)
        gap<d = ¬gapped
        gap'-upper-bound =
            start
                ⟦ next ⟧ * suc b ∸ ⟦ xs ⟧ * suc b
            ≈⟨ sym (*-distrib-∸ʳ (suc b) ⟦ next ⟧ ⟦ xs ⟧) ⟩
                (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b
            ≤⟨ gap<d ⟩
                suc d
            ≤⟨ m≤m+n (suc d) o ⟩
                suc d + o
            ≈⟨ cong (λ w → w + o) (sym greatest) ⟩
                suc (Digit-toℕ x o)
            □
        next>this = <⇒≤ $ next-number-is-greater-Others xs ¬max d+o≥2
    in
    start
        ⟦ digit+1-n x greatest gap gap>0 ∷ next ⟧
    ≈⟨ cong (λ w → w + ⟦ next ⟧ * suc b) (Digit-toℕ-digit+1-n x greatest gap gap>0 gap<d) ⟩
        suc (Digit-toℕ x o) ∸ gap + ⟦ next ⟧ * suc b
    ≈⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + ⟦ next ⟧ * suc b) (*-distrib-∸ʳ (suc b) ⟦ next ⟧ ⟦ xs ⟧) ⟩
        suc (Digit-toℕ x o) ∸ (⟦ next ⟧ * suc b ∸ ⟦ xs ⟧ * suc b) + ⟦ next ⟧ * suc b
    ≈⟨ m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ xs ⟧ * suc b) (⟦ next ⟧ * suc b) (*n-mono (suc b) next>this) gap'-upper-bound ⟩
        suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
    ≤⟨ prop ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
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
next-number-is-LUB xs ys ¬max prop | Others b d o d+o≥2 = next-number-is-LUB-Others xs ys ¬max d+o≥2 prop

-- begin
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ∎

-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- □
