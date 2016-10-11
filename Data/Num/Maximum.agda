module Data.Num.Maximum where

open import Data.Num.Core
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

Maximum-unique : ∀ {b d o}
    → (max xs : Num b d o)
    → (max! : ¬ (Null max))
    → (xs! : ¬ (Null xs))
    → Maximum max max!
    → Maximum xs xs!
    → ⟦ max ⟧ max! ≡ ⟦ xs ⟧ xs!
Maximum-unique max xs max! xs! max-max xs-max = IsPartialOrder.antisym isPartialOrder
    (xs-max max max!)
    (max-max xs xs!)

Maximum? : ∀ {b d o}
    → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → Dec (Maximum xs xs!)
Maximum? {b} {d} {o} xs xs! with boundedView b d o
Maximum? xs xs! | IsBounded cond with BoundedCond⇒Bounded cond
Maximum? xs xs! | IsBounded cond | max , max! , claim with ⟦ max ⟧ max! ≟ ⟦ xs ⟧ xs!
Maximum? xs xs! | IsBounded cond | max , max! , claim | yes p rewrite p = yes claim
Maximum? xs xs! | IsBounded cond | max , max! , claim | no ¬p = no (contraposition (Maximum-unique max xs max! xs! claim) ¬p)
Maximum? xs xs! | IsntBounded cond = no (¬Bounded⇒¬Maximum (NonBoundedCond⇒¬Bounded cond) xs xs!)

data Base≡0-View : ℕ → ℕ → Set where
    HasOnly0 :                                  Base≡0-View 0 0
    Others : ∀ {d o} → (bound : d + o ≥ 1 ⊔ o) → Base≡0-View d o

Base≡0-view : ∀ d o → Base≡0-View d o
Base≡0-view zero    zero     = HasOnly0
Base≡0-view zero    (suc o)  = Others (s≤s ≤-refl)
Base≡0-view (suc d) zero     = Others (s≤s z≤n)
Base≡0-view (suc d) (suc o)  = Others (m≤n+m (suc o) (suc d))

next-number-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (xs! : ¬ (Null xs))
    → ¬ (Maximum xs xs!)
    → Num 0 (suc d) o
next-number-Base≡0 {d} {o} xs xs! ¬max with Base≡0-view d o
next-number-Base≡0 xs       xs! ¬max | HasOnly0 = contradiction (HasOnly0-Maximum xs xs!) ¬max
next-number-Base≡0 ∙        xs! ¬max | Others bound = contradiction tt xs!
next-number-Base≡0 (x ∷ xs) xs! ¬max | Others bound with Greatest? x
next-number-Base≡0 (x ∷ xs) xs! ¬max | Others bound | yes greatest = contradiction (Base≡0-Maximum x xs greatest) ¬max
next-number-Base≡0 (x ∷ xs) xs! ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∷ xs

next-number-HasOnly0 : ∀ {b}
    → (xs : Num (suc b) 1 0)
    → (xs! : ¬ (Null xs))
    → ¬ (Maximum xs xs!)
    → Num (suc b) 1 0
next-number-HasOnly0 {b} xs xs! ¬max = contradiction (HasOnly0-Maximum xs xs!) ¬max



next-number-1⊔o-upper-bound : ∀ m n → 2 ≤ suc m + n → m + n ≥ 1 ⊔ n
next-number-1⊔o-upper-bound m zero    q = ≤-pred q
next-number-1⊔o-upper-bound m (suc n) q = m≤n+m (suc n) m

mutual

    next-number-¬Maximum : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (xs! : ¬ (Null xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → ¬ (Maximum xs xs!)
    next-number-¬Maximum {b} {d} {o} xs xs! d+o≥2 = ¬Bounded⇒¬Maximum (Digit+Offset≥2-¬Bounded b d o (≤-pred d+o≥2)) xs xs!

    Gapped : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (xs! : ¬ (Null xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Set
    Gapped {b} {d} {o} xs xs! d+o≥2 =
        let
            ¬max = next-number-¬Maximum xs xs! d+o≥2
            next! = next-number-¬Null-d+o≥2 xs xs! ¬max d+o≥2
            next = next-number-d+o≥2 xs xs! ¬max d+o≥2
        in
            suc d ≤ (⟦ next ⟧ next! ∸ ⟦ xs ⟧ xs!) * suc b

    Gapped? : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (xs! : ¬ (Null xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Dec (Gapped xs xs! d+o≥2)
    Gapped? {b} {d} {o} xs xs! d+o≥2 =
        let
            ¬max = next-number-¬Maximum xs xs! d+o≥2
            next! = next-number-¬Null-d+o≥2 xs xs! ¬max d+o≥2
            next = next-number-d+o≥2 xs xs! ¬max d+o≥2
        in
            suc d ≤? (⟦ next ⟧ next! ∸ ⟦ xs ⟧ xs!) * suc b

    -- 1 `max` o, in case that the least digit "o" is 0, which is too small
    1⊔o : ∀ d o → 2 ≤ suc (d + o) → Digit (suc d)
    1⊔o d o d+o≥2 = Digit-fromℕ (1 ⊔ o) o (next-number-1⊔o-upper-bound d o d+o≥2)


    -- the actual function
    next-number-d+o≥2 : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (xs! : ¬ (Null xs))
        → ¬ (Maximum xs xs!)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Num (suc b) (suc d) o
    next-number-d+o≥2 {b} {d} {o} ∙ xs! ¬max prop = contradiction tt xs!
    next-number-d+o≥2 {b} {d} {o} (x ∷ xs)      xs! ¬max prop with Greatest? x
    next-number-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest with suc d ≤? (1 ⊔ o) * suc b
    next-number-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | yes gapped = z ∷ 1⊔o d o prop ∷ ∙
    next-number-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | no ¬gapped =
        let lower-bound : (1 ⊔ o) * suc b > 0
            lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n
        in  digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ 1⊔o d o prop ∷ ∙
    next-number-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest with Gapped? (x' ∷ xs) id prop
    next-number-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | yes gapped =
        let
            ¬max = next-number-¬Maximum (x' ∷ xs) id prop
            next = next-number-d+o≥2 (x' ∷ xs) id ¬max prop
        in z ∷ next
    next-number-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | no ¬gapped =
        let
            ¬max = next-number-¬Maximum (x' ∷ xs) id prop
            next = next-number-d+o≥2 (x' ∷ xs) id ¬max prop
            next! = next-number-¬Null-d+o≥2 (x' ∷ xs) id ¬max prop
            gap = (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) * suc b
            gap>0 = (start
                    1
                ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ x' ∷ xs ⟧))) ⟩
                    suc (⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧)
                ≈⟨ sym (+-∸-assoc 1 {⟦ x' ∷ xs ⟧} ≤-refl) ⟩
                    suc ⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧
                ≤⟨ ∸-mono {suc ⟦ x' ∷ xs ⟧} {⟦ next ⟧ next!} {⟦ x' ∷ xs ⟧} (next-number-is-greater-d+o≥2 (x' ∷ xs) id ¬max prop) ≤-refl ⟩
                    ⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧
                □) *-mono (s≤s {0} {b} z≤n)
        in digit+1-n x greatest gap gap>0 ∷ next
    next-number-d+o≥2 {b} {d} {o} (x ∷ xs)      xs! ¬max prop | no ¬greatest
        = digit+1 x ¬greatest ∷ xs

    -- properties of the actual function
    next-number-¬Null-d+o≥2 : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (xs! : ¬ (Null xs))
        → (¬max : ¬ (Maximum xs xs!))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → ¬ Null (next-number-d+o≥2 xs xs! ¬max d+o≥2)
    next-number-¬Null-d+o≥2 {b} {d} {o} ∙ xs! ¬max prop = contradiction tt xs!
    next-number-¬Null-d+o≥2 {b} {d} {o} (x ∷ xs)      xs! ¬max prop with Greatest? x
    next-number-¬Null-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest with suc d ≤? (1 ⊔ o) * suc b
    next-number-¬Null-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | yes gapped = id
    next-number-¬Null-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | no ¬gapped = id
    next-number-¬Null-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest with Gapped? (x' ∷ xs) id prop
    next-number-¬Null-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | yes gapped = id
    next-number-¬Null-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | no ¬gapped = id
    next-number-¬Null-d+o≥2 {b} {d} {o} (x ∷ xs)      xs! ¬max prop | no ¬greatest = id
    -- next-number-¬Null-d+o≥2 {b} {d} {o} (x ∷ xs)       xs! ¬max prop | no ¬greatest = {!   !}

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

    next-number-is-greater-d+o≥2 : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (xs! : ¬ (Null xs))
        → (¬max : ¬ (Maximum xs xs!))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → ⟦ next-number-d+o≥2 xs xs! ¬max d+o≥2 ⟧ next-number-¬Null-d+o≥2 xs xs! ¬max d+o≥2 > ⟦ xs ⟧ xs!
    next-number-is-greater-d+o≥2 {b} {d} {o} ∙ xs! ¬max prop = contradiction tt xs!
    next-number-is-greater-d+o≥2 {b} {d} {o} (x ∷ xs)      xs! ¬max prop with Greatest? x
    next-number-is-greater-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest with suc d ≤? (1 ⊔ o) * suc b
    next-number-is-greater-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | yes gapped =
        start
            suc (Fin.toℕ x + o)
        ≈⟨ cong (λ w → w + o) greatest ⟩
            suc d + o
        ≈⟨ +-comm (suc d) o ⟩
            o + suc d
        ≤⟨ n+-mono o gapped ⟩
            o + (suc zero ⊔ o) * suc b
        ≈⟨ cong (λ w → o + w * suc b) (sym (Digit-toℕ-1⊔o d o prop)) ⟩
            o + (Digit-toℕ (1⊔o d o prop) o) * suc b
        □
    next-number-is-greater-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | no ¬gapped =
        let
            lower-bound : (suc zero ⊔ o) * suc b ≤ suc d
            lower-bound = ≤-pred $ ≤-step $ ≰⇒> ¬gapped
            upper-bound : 1 ≤ (suc zero ⊔ o) * suc b
            upper-bound = m≤m⊔n (suc zero) o *-mono s≤s z≤n
            prop2 : (suc zero ⊔ o) * suc b ≤ suc (Digit-toℕ x o)
            prop2 = ≤-pred $
                start
                    suc ((suc zero ⊔ o) * suc b)
                ≤⟨ ≰⇒> ¬gapped ⟩
                    suc d
                ≈⟨ sym greatest ⟩
                    suc (Fin.toℕ x)
                ≤⟨ ≤-step (m≤m+n (suc (Fin.toℕ x)) o) ⟩
                    suc (suc (Fin.toℕ x + o))
                □
        in start
            suc (Fin.toℕ x + o)
        ≈⟨ sym (m∸n+n≡m {_} {(suc zero ⊔ o) * suc b} prop2) ⟩
            suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + (suc zero ⊔ o) * suc b
        ≈⟨ cong (λ w → suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + w * suc b) (sym (Digit-toℕ-1⊔o d o prop)) ⟩
            suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + (Digit-toℕ (1⊔o d o prop) o) * suc b
        ≈⟨ cong (λ w → w + (Digit-toℕ (1⊔o d o prop) o) * suc b) (sym (Digit-toℕ-digit+1-n x greatest ((1 ⊔ o) * suc b) upper-bound lower-bound)) ⟩
            Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) upper-bound) o + (Digit-toℕ (1⊔o d o prop) o) * suc b
        □
    next-number-is-greater-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest with Gapped? (x' ∷ xs) id prop
    next-number-is-greater-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | yes gapped =
    -- suc (Fin.toℕ x + o + (⟦ x' ∷ xs ⟧ xs!) * suc b) ≤ ⟦ z ∷ next ⟧ id
        let
            ¬max = next-number-¬Maximum (x' ∷ xs) id prop
            next  = next-number-d+o≥2 (x' ∷ xs) id ¬max prop
            next! = next-number-¬Null-d+o≥2 (x' ∷ xs) id ¬max prop

            next>this = ≤-pred $ ≤-step $ next-number-is-greater-d+o≥2 (x' ∷ xs) id ¬max prop
        in
            start
                suc (Digit-toℕ x o) + ⟦ x' ∷ xs ⟧ * suc b
            ≈⟨ cong (λ w → suc w + ⟦ x' ∷ xs ⟧ * suc b) (toℕ-greatest x greatest) ⟩
                suc d + o + ⟦ x' ∷ xs ⟧ * suc b
            ≈⟨ +-assoc (suc d) o (⟦ x' ∷ xs ⟧ * suc b) ⟩
                suc d + (o + ⟦ x' ∷ xs ⟧ * suc b)
            ≈⟨ a+[b+c]≡b+[a+c] (suc d) o (⟦ x' ∷ xs ⟧ * suc b) ⟩
                o + (suc d + ⟦ x' ∷ xs ⟧ * suc b)
            ≤⟨ n+-mono o (+n-mono (⟦ x' ∷ xs ⟧ * suc b) gapped) ⟩
                o + ((⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) * suc b + ⟦ x' ∷ xs ⟧ * suc b)
            ≈⟨ cong (λ w → o + w) (sym (distribʳ-*-+ (suc b) (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) ⟦ x' ∷ xs ⟧)) ⟩
                o + (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧ + ⟦ x' ∷ xs ⟧) * suc b
            ≈⟨ cong (λ w → o + w * suc b) (m∸n+n≡m next>this) ⟩
                o + (⟦ next ⟧ next!) * suc b
            ≈⟨ sym (expand z next next!)  ⟩
                ⟦ z ∷ next ⟧
            □
    next-number-is-greater-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | no ¬gapped =
    -- suc (Fin.toℕ x + o + (⟦ x' ∷ xs ⟧ xs!) * suc b) ≤ ⟦ digit+1-n x greatest gap gap>0 ∷ next-xs ⟧ id
        let
            ¬max = next-number-¬Maximum (x' ∷ xs) id prop
            next = next-number-d+o≥2 (x' ∷ xs) id ¬max prop
            next! = next-number-¬Null-d+o≥2 (x' ∷ xs) id ¬max prop
            gap = (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) * suc b
            gap>0 = (start
                    1
                ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ x' ∷ xs ⟧))) ⟩
                    suc (⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧)
                ≈⟨ sym (+-∸-assoc 1 {⟦ x' ∷ xs ⟧} ≤-refl) ⟩
                    suc ⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧
                ≤⟨ ∸-mono {suc ⟦ x' ∷ xs ⟧} {⟦ next ⟧ next!} {⟦ x' ∷ xs ⟧} (next-number-is-greater-d+o≥2 (x' ∷ xs) id ¬max prop) ≤-refl ⟩
                    ⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧
                □) *-mono (s≤s {0} {b} z≤n)
            gap<d = ≤-pred $ ≤-step $ ≰⇒> ¬gapped
            gap'-upper-bound =
                start
                    ⟦ next ⟧ next! * suc b ∸ ⟦ x' ∷ xs ⟧ * suc b
                ≈⟨ sym (*-distrib-∸ʳ (suc b) (⟦ next ⟧ next!) ⟦ x' ∷ xs ⟧) ⟩
                    (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) * suc b
                ≤⟨ gap<d ⟩
                    suc d
                ≤⟨ m≤m+n (suc d) o ⟩
                    suc d + o
                ≈⟨ cong (λ w → w + o) (sym greatest) ⟩
                    suc (Digit-toℕ x o)
                □
            LSD = digit+1-n x greatest gap gap>0
            next>this = ≤-pred $ ≤-step $ next-number-is-greater-d+o≥2 (x' ∷ xs) id ¬max prop

        in start
            suc (Digit-toℕ x o) + ⟦ x' ∷ xs ⟧ * suc b
        ≈⟨ sym (m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ x' ∷ xs ⟧ * suc b) (⟦ next ⟧ next! * suc b) (*n-mono (suc b) next>this) gap'-upper-bound) ⟩
            suc (Digit-toℕ x o) ∸ (⟦ next ⟧ next! * suc b ∸ ⟦ x' ∷ xs ⟧ * suc b) + (⟦ next ⟧ next!) * suc b
        ≈⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + (⟦ next ⟧ next!) * suc b) (sym (*-distrib-∸ʳ (suc b) (⟦ next ⟧ next!) ⟦ x' ∷ xs ⟧)) ⟩
            suc (Digit-toℕ x o) ∸ (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) * suc b + (⟦ next ⟧ next!) * suc b
        ≈⟨ cong (λ w → w + ⟦ next ⟧ next! * suc b) (sym (Digit-toℕ-digit+1-n x greatest gap gap>0 gap<d)) ⟩
            Digit-toℕ LSD o + ⟦ next ⟧ next! * suc b
        ≈⟨ sym (expand LSD next next!) ⟩
            ⟦ LSD ∷ next ⟧
        □
    next-number-is-greater-d+o≥2 {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | no ¬greatest
        = reflexive $ sym (Digit-toℕ-digit+1 x ¬greatest)
    next-number-is-greater-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | no ¬greatest =
        start
            suc ⟦ x ∷ (x' ∷ xs) ⟧
        ≈⟨ cong (λ w → w + ⟦ x' ∷ xs ⟧ * suc b) (sym (Digit-toℕ-digit+1 x ¬greatest)) ⟩
            Digit-toℕ (digit+1 x ¬greatest) o + ⟦ x' ∷ xs ⟧ * suc b
        ≈⟨ sym (expand (digit+1 x ¬greatest) (x' ∷ xs) id) ⟩
            ⟦ digit+1 x ¬greatest ∷ (x' ∷ xs) ⟧
        □

next-number-HasNoDigit : ∀ {b o}
    → (xs : Num b 0 o)
    → (xs! : ¬ (Null xs))
    → ¬ (Maximum xs xs!)
    → Num b 0 o
next-number-HasNoDigit xs xs! ¬max = HasNoDigit-explode xs xs!


next-number : ∀ {b d o}
    → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → ¬ (Maximum xs xs!)
    → Num b d o
next-number {b} {d} {o} xs xs! ¬max with boundedView b d o
next-number xs xs! ¬max | IsBounded   (Base≡0 d o) = next-number-Base≡0 xs xs! ¬max
next-number xs xs! ¬max | IsBounded   (HasOnly0 b) = next-number-HasOnly0 xs xs! ¬max
next-number xs xs! ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-d+o≥2 xs xs! ¬max d+o≥2
next-number xs xs! ¬max | IsntBounded (HasNoDigit b o) = next-number-HasNoDigit xs xs! ¬max

next-number-¬Null-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ¬ Null (next-number-Base≡0 xs xs! ¬max)
next-number-¬Null-Base≡0 {d} {o} xs xs! ¬max with Base≡0-view d o
next-number-¬Null-Base≡0 xs       xs! ¬max | HasOnly0 = contradiction (HasOnly0-Maximum xs xs!) ¬max
next-number-¬Null-Base≡0 ∙        xs! ¬max | Others bound = contradiction tt xs!
next-number-¬Null-Base≡0 (x ∷ xs) xs! ¬max | Others bound with Greatest? x
next-number-¬Null-Base≡0 (x ∷ xs) xs! ¬max | Others bound | yes greatest = contradiction (Base≡0-Maximum x xs greatest) ¬max
next-number-¬Null-Base≡0 (x ∷ xs) xs! ¬max | Others bound | no ¬greatest = id

next-number-¬Null-HasOnly0 : ∀ {b}
    → (xs : Num (suc b) 1 0)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ¬ Null (next-number-HasOnly0 xs xs! ¬max)
next-number-¬Null-HasOnly0 {b} xs xs! ¬max = contradiction (HasOnly0-Maximum xs xs!) ¬max

next-number-¬Null-HasNoDigit : ∀ {b o}
    → (xs : Num b 0 o)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ¬ Null (next-number-HasNoDigit xs xs! ¬max)
next-number-¬Null-HasNoDigit xs xs! ¬max = HasNoDigit-explode xs xs!

next-number-¬Null : ∀ {b d o}
    → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ¬ Null (next-number xs xs! ¬max)
next-number-¬Null {b} {d} {o} xs xs! ¬max with boundedView b d o
next-number-¬Null xs xs! ¬max | IsBounded (Base≡0 d o) = next-number-¬Null-Base≡0 xs xs! ¬max
next-number-¬Null xs xs! ¬max | IsBounded (HasOnly0 b) = next-number-¬Null-HasOnly0 xs xs! ¬max
next-number-¬Null xs xs! ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-¬Null-d+o≥2 xs xs! ¬max d+o≥2
next-number-¬Null xs xs! ¬max | IsntBounded (HasNoDigit b o) = next-number-¬Null-HasNoDigit xs xs! ¬max

next-number-is-greater-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ next-number-Base≡0 xs xs! ¬max ⟧ next-number-¬Null-Base≡0 xs xs! ¬max > ⟦ xs ⟧ xs!
next-number-is-greater-Base≡0 {d} {o} xs    xs! ¬max with Base≡0-view d o
next-number-is-greater-Base≡0 xs            xs! ¬max | HasOnly0 = contradiction (HasOnly0-Maximum xs xs!) ¬max
next-number-is-greater-Base≡0 ∙             xs! ¬max | Others bound = contradiction tt xs!
next-number-is-greater-Base≡0 (x ∷ xs)      xs! ¬max | Others bound with Greatest? x
next-number-is-greater-Base≡0 (x ∷ xs)      xs! ¬max | Others bound | yes greatest = contradiction (Base≡0-Maximum x xs greatest) ¬max
next-number-is-greater-Base≡0 (x ∷ ∙)       xs! ¬max | Others bound | no ¬greatest = reflexive (sym (Digit-toℕ-digit+1 x ¬greatest))
next-number-is-greater-Base≡0 (x ∷ x' ∷ xs) xs! ¬max | Others bound | no ¬greatest = +n-mono (⟦ x' ∷ xs ⟧ * 0) (reflexive (sym (Digit-toℕ-digit+1 x ¬greatest)))

next-number-is-greater-HasOnly0 : ∀ {b}
    → (xs : Num (suc b) 1 0)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ next-number-HasOnly0 xs xs! ¬max ⟧ next-number-¬Null-HasOnly0 xs xs! ¬max > ⟦ xs ⟧ xs!
next-number-is-greater-HasOnly0 {b} xs xs! ¬max = contradiction (HasOnly0-Maximum xs xs!) ¬max


next-number-is-greater-HasNoDigit : ∀ {b o}
    → (xs : Num b 0 o)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ next-number-HasNoDigit xs xs! ¬max ⟧ next-number-¬Null-HasNoDigit xs xs! ¬max > ⟦ xs ⟧ xs!
next-number-is-greater-HasNoDigit {b} xs xs! ¬max = HasNoDigit-explode xs xs!

next-number-is-greater : ∀ {b d o}
    → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ next-number xs xs! ¬max ⟧ next-number-¬Null xs xs! ¬max > ⟦ xs ⟧ xs!
next-number-is-greater {b} {d} {o} xs xs! ¬max with boundedView b d o
next-number-is-greater xs xs! ¬max | IsBounded (Base≡0 d o) = next-number-is-greater-Base≡0 xs xs! ¬max
next-number-is-greater xs xs! ¬max | IsBounded (HasOnly0 b) = next-number-is-greater-HasOnly0 xs xs! ¬max
next-number-is-greater xs xs! ¬max | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-is-greater-d+o≥2 xs xs! ¬max d+o≥2
next-number-is-greater xs xs! ¬max | IsntBounded (HasNoDigit b o) = next-number-is-greater-HasNoDigit xs xs! ¬max

next-number-is-LUB-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (ys : Num 0 (suc d) o)
    → (xs! : ¬ (Null xs))
    → (ys! : ¬ (Null ys))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ ys ⟧ ys! > ⟦ xs ⟧ xs!
    → ⟦ ys ⟧ ys! ≥ ⟦ next-number-Base≡0 xs xs! ¬max ⟧ next-number-¬Null-Base≡0 xs xs! ¬max
next-number-is-LUB-Base≡0 {d} {o} xs ys xs! ys! ¬max prop with Base≡0-view d o
next-number-is-LUB-Base≡0 {0} {0} xs ys xs! ys! ¬max prop | HasOnly0 = contradiction (HasOnly0-Maximum xs xs!) ¬max
next-number-is-LUB-Base≡0         ∙  ys xs! ys! ¬max prop | Others bound = contradiction tt xs!
next-number-is-LUB-Base≡0 {d} {o} (x ∷ xs) ∙ xs! ys! ¬max prop | Others bound = contradiction tt ys!
next-number-is-LUB-Base≡0 {d} {o} (x ∷ xs) (y ∷ ys) xs! ys! ¬max prop | Others bound with Greatest? x
next-number-is-LUB-Base≡0 {d} {o} (x ∷ xs) (y ∷ ys) xs! ys! ¬max prop | Others bound | yes greatest = contradiction (Base≡0-Maximum x xs greatest) ¬max
next-number-is-LUB-Base≡0 {d} {o} (x ∷ ∙) (y ∷ ys) xs! ys! ¬max prop | Others bound | no ¬greatest =
    start
        Digit-toℕ (digit+1 x ¬greatest) o
    ≈⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Digit-toℕ x o)
    ≤⟨ prop ⟩
        ⟦ y ∷ ys ⟧
    □
next-number-is-LUB-Base≡0 {d} {o} (x ∷ x' ∷ xs) (y ∷ ys) xs! ys! ¬max prop | Others bound | no ¬greatest =
    start
        ⟦ digit+1 x ¬greatest ∷ (x' ∷ xs) ⟧
    ≈⟨ expand (digit+1 x ¬greatest) (x' ∷ xs) id ⟩
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ x' ∷ xs ⟧ * 0
    ≈⟨ cong (λ w → w + ⟦ x' ∷ xs ⟧ * 0) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Digit-toℕ x o) + ⟦ x' ∷ xs ⟧ * 0
    ≤⟨ prop ⟩
        ⟦ y ∷ ys ⟧
    □

next-number-is-LUB-HasOnly0 : ∀ {b}
    → (xs : Num (suc b) 1 0)
    → (ys : Num (suc b) 1 0)
    → (xs! : ¬ (Null xs))
    → (ys! : ¬ (Null ys))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ ys ⟧ ys! > ⟦ xs ⟧ xs!
    → ⟦ ys ⟧ ys! ≥ ⟦ next-number-HasOnly0 xs xs! ¬max ⟧ next-number-¬Null-HasOnly0 xs xs! ¬max
next-number-is-LUB-HasOnly0 {b} xs ys xs! ys! ¬max prop = contradiction (HasOnly0-Maximum xs xs!) ¬max

≥1⊔o : ∀ {d o b}
    → (xs : Num (suc b) (suc d) o)
    → (xs! : ¬ (Null xs))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ⟦ xs ⟧ xs! ≥ 1
    → ⟦ xs ⟧ xs! ≥ 1 ⊔ o
≥1⊔o {_}             ∙             xs! d+o≥2 prop = contradiction tt xs!
≥1⊔o {_} {zero}      (x ∷ xs)      xs! d+o≥2 prop = prop
≥1⊔o {d} {suc o}     (x ∷ ∙)       xs! d+o≥2 prop = m≤n+m (suc o) (Fin.toℕ x)
≥1⊔o {d} {suc o} {b} (x ∷ x' ∷ xs) xs! d+o≥2 prop =
    start
        suc o
    ≤⟨ m≤n+m (suc o) (Fin.toℕ x) ⟩
        Fin.toℕ x + suc o
    ≤⟨ m≤m+n (Fin.toℕ x + suc o) (⟦ x' ∷ xs ⟧ * suc b) ⟩
        Fin.toℕ x + suc o + ⟦ x' ∷ xs ⟧ * suc b
    □

next-number-is-LUB-d+o≥2 : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (ys : Num (suc b) (suc d) o)
    → (xs! : ¬ (Null xs))
    → (ys! : ¬ (Null ys))
    → (¬max : ¬ (Maximum xs xs!))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ⟦ ys ⟧ ys! > ⟦ xs ⟧ xs!
    → ⟦ ys ⟧ ys! ≥ ⟦ next-number-d+o≥2 xs xs! ¬max d+o≥2 ⟧ next-number-¬Null-d+o≥2 xs xs! ¬max d+o≥2
-- next-number-is-LUB-d+o≥2 xs ys xs! ys! ¬max d+o≥2 = {!   !}
next-number-is-LUB-d+o≥2 {b} {d} {o} ∙ ys xs! ys! ¬max d+o≥2 prop = contradiction tt xs!
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ xs) ys xs! ys! ¬max d+o≥2 prop with Greatest? x
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ ∙) ys xs! ys! ¬max d+o≥2 prop | yes greatest with suc d ≤? (1 ⊔ o) * suc b
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ ∙)        ∙ xs! ys! ¬max d+o≥2 prop | yes greatest | yes gapped = contradiction tt ys!
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ ∙) (y ∷ ∙) xs! ys! ¬max d+o≥2 prop | yes greatest | yes gapped = contradiction prop (>⇒≰ (s≤s (greatest-of-all o x y greatest)))
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ ∙) (y ∷ y' ∷ ys) xs! ys! ¬max d+o≥2 prop | yes greatest | yes gapped =
    let
        ⟦ys⟧>0 = tail-mono-strict-Null x y (y' ∷ ys) id greatest prop
    in
    start
        o + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
    ≈⟨ cong (λ w → o + w * suc b) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
        o + (1 ⊔ o) * suc b
    ≤⟨ n+-mono o (*n-mono (suc b) (≥1⊔o (y' ∷ ys) id d+o≥2 ⟦ys⟧>0)) ⟩
        o + ⟦ y' ∷ ys ⟧ * suc b
    ≤⟨ +n-mono (⟦ y' ∷ ys ⟧ * suc b) (m≤n+m o (Fin.toℕ y)) ⟩
        Digit-toℕ y o + ⟦ y' ∷ ys ⟧ * suc b
    □
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ ∙) ∙ xs! ys! ¬max d+o≥2 prop | yes greatest | no ¬gapped = contradiction tt ys!
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ ∙) (y ∷ ∙) xs! ys! ¬max d+o≥2 prop | yes greatest | no ¬gapped = contradiction prop (>⇒≰ (s≤s (greatest-of-all o x y greatest)))
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ ∙) (y ∷ y' ∷ ys) xs! ys! ¬max d+o≥2 prop | yes greatest | no ¬gapped =
    let
        lower-bound : (1 ⊔ o) * suc b > 0
        lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n
        upper-bound : (1 ⊔ o) * suc b ≤ suc d
        upper-bound = ≤-pred $ ≤-step $ ≰⇒> ¬gapped
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
        Digit-toℕ y o + ⟦ y' ∷ ys ⟧ * suc b
    □
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) ys xs! ys! ¬max d+o≥2 prop | yes greatest with Gapped? (x' ∷ xs) id d+o≥2
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) ∙ xs! ys! ¬max d+o≥2 prop | yes greatest | yes gapped = contradiction tt ys!
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) (y ∷ ∙) xs! ys! ¬max d+o≥2 prop | yes greatest | yes gapped = contradiction prop $ >⇒≰ $
    start
        suc (Fin.toℕ y + o)
    ≤⟨ s≤s (greatest-of-all o x y greatest) ⟩
        suc (Fin.toℕ x + o)
    ≤⟨ m≤m+n (suc (Fin.toℕ x + o)) (⟦ x' ∷ xs ⟧ * suc b) ⟩
        suc (Fin.toℕ x + o + ⟦ x' ∷ xs ⟧ * suc b)
    □
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) (y ∷ y' ∷ ys) xs! ys! ¬max d+o≥2 prop | yes greatest | yes gapped =
    let
        ¬max = next-number-¬Maximum (x' ∷ xs) id d+o≥2
        next = next-number-d+o≥2 (x' ∷ xs) id ¬max d+o≥2
        next! = next-number-¬Null-d+o≥2 (x' ∷ xs) id ¬max d+o≥2
        ⟦y'∷ys⟧>⟦x'∷xs⟧ = tail-mono-strict x (x' ∷ xs) y (y' ∷ ys) id id greatest prop
    in
    start
        -- Digit-toℕ {! z  !} o + (⟦ next ⟧ next!) * suc b
    -- ≈⟨ {!   !} ⟩
        ⟦ z ∷ next ⟧
    ≈⟨ expand z next next! ⟩
        o + (⟦ next ⟧ next!) * suc b
    ≤⟨ n+-mono o (*n-mono (suc b) (next-number-is-LUB-d+o≥2 (x' ∷ xs) (y' ∷ ys) id id ¬max d+o≥2 ⟦y'∷ys⟧>⟦x'∷xs⟧)) ⟩
        o + ⟦ y' ∷ ys ⟧ * suc b
    ≤⟨ +n-mono (⟦ y' ∷ ys ⟧ * suc b) (m≤n+m o (Fin.toℕ y)) ⟩
        Digit-toℕ y o + ⟦ y' ∷ ys ⟧ * suc b
    □
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) ∙ xs! ys! ¬max d+o≥2 prop | yes greatest | no ¬gapped = contradiction tt ys!
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) (y ∷ ∙) xs! ys! ¬max d+o≥2 prop | yes greatest | no ¬gapped = contradiction prop $ >⇒≰ $
    start
        suc (Fin.toℕ y + o)
    ≤⟨ s≤s (greatest-of-all o x y greatest) ⟩
        suc (Fin.toℕ x + o)
    ≤⟨ m≤m+n (suc (Fin.toℕ x + o)) (⟦ x' ∷ xs ⟧ * suc b) ⟩
        suc (Fin.toℕ x + o + ⟦ x' ∷ xs ⟧ * suc b)
    □
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) (y ∷ y' ∷ ys) xs! ys! ¬max d+o≥2 prop | yes greatest | no ¬gapped =
    let
        ¬max = next-number-¬Maximum (x' ∷ xs) id d+o≥2
        next = next-number-d+o≥2 (x' ∷ xs) id ¬max d+o≥2
        next! = next-number-¬Null-d+o≥2 (x' ∷ xs) id ¬max d+o≥2
        gap = (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) * suc b
        gap>0 = (start
                1
            ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ x' ∷ xs ⟧))) ⟩
                suc (⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧)
            ≈⟨ sym (+-∸-assoc 1 {⟦ x' ∷ xs ⟧} ≤-refl) ⟩
                suc ⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧
            ≤⟨ ∸-mono {suc ⟦ x' ∷ xs ⟧} {⟦ next ⟧ next!} {⟦ x' ∷ xs ⟧} (next-number-is-greater-d+o≥2 (x' ∷ xs) id ¬max d+o≥2) ≤-refl ⟩
                ⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧
            □) *-mono (s≤s {0} {b} z≤n)
        gap<d = ≤-pred $ ≤-step $ ≰⇒> ¬gapped
        gap'-upper-bound =
            start
                ⟦ next ⟧ next! * suc b ∸ ⟦ x' ∷ xs ⟧ * suc b
            ≈⟨ sym (*-distrib-∸ʳ (suc b) (⟦ next ⟧ next!) ⟦ x' ∷ xs ⟧) ⟩
                (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) * suc b
            ≤⟨ gap<d ⟩
                suc d
            ≤⟨ m≤m+n (suc d) o ⟩
                suc d + o
            ≈⟨ cong (λ w → w + o) (sym greatest) ⟩
                suc (Digit-toℕ x o)
            □
        next>this = ≤-pred $ ≤-step $ next-number-is-greater-d+o≥2 (x' ∷ xs) id ¬max d+o≥2
    in
    start
        ⟦ digit+1-n x greatest gap gap>0 ∷ next ⟧
    ≈⟨ expand (digit+1-n x greatest gap gap>0) next next! ⟩
        Digit-toℕ (digit+1-n x greatest gap gap>0) o + (⟦ next ⟧ next!) * suc b
    ≈⟨ cong (λ w → w + (⟦ next ⟧ next!) * suc b) (Digit-toℕ-digit+1-n x greatest gap gap>0 gap<d) ⟩
        suc (Digit-toℕ x o) ∸ gap + (⟦ next ⟧ next!) * suc b
    ≈⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + (⟦ next ⟧ next!) * suc b) (*-distrib-∸ʳ (suc b) (⟦ next ⟧ next!) ⟦ x' ∷ xs ⟧) ⟩
        suc (Digit-toℕ x o) ∸ (⟦ next ⟧ next! * suc b ∸ ⟦ x' ∷ xs ⟧ * suc b) + (⟦ next ⟧ next!) * suc b
    ≈⟨ m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ x' ∷ xs ⟧ * suc b) (⟦ next ⟧ next! * suc b) (*n-mono (suc b) next>this) gap'-upper-bound ⟩
        suc (Digit-toℕ x o) + ⟦ x' ∷ xs ⟧ * suc b
    ≤⟨ prop ⟩
        Digit-toℕ y o + ⟦ y' ∷ ys ⟧ * suc b
    □
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ xs) ∙ xs! ys! ¬max d+o≥2 prop | no ¬greatest = contradiction tt ys!
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ ∙) (y ∷ ys) xs! ys! ¬max d+o≥2 prop | no ¬greatest =
    start
        Digit-toℕ (digit+1 x ¬greatest) o
    ≈⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Digit-toℕ x o)
    ≤⟨ prop ⟩
        ⟦ y ∷ ys ⟧
    □
next-number-is-LUB-d+o≥2 {b} {d} {o} (x ∷ x' ∷ xs) (y ∷ ys) xs! ys! ¬max d+o≥2 prop | no ¬greatest =
    start
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ x' ∷ xs ⟧ * suc b
    ≈⟨ cong (λ w → w + ⟦ x' ∷ xs ⟧ * suc b) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Digit-toℕ x o) + ⟦ x' ∷ xs ⟧ * suc b
    ≤⟨ prop ⟩
        ⟦ y ∷ ys ⟧
    □

next-number-is-LUB-HasNoDigit : ∀ {b o}
    → (xs : Num b 0 o)
    → (ys : Num b 0 o)
    → (xs! : ¬ (Null xs))
    → (ys! : ¬ (Null ys))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ ys ⟧ ys! > ⟦ xs ⟧ xs!
    → ⟦ ys ⟧ ys! ≥ ⟦ next-number-HasNoDigit xs xs! ¬max ⟧ next-number-¬Null-HasNoDigit xs xs! ¬max
next-number-is-LUB-HasNoDigit xs _ xs! _ _ _ = HasNoDigit-explode xs xs!

next-number-is-LUB : ∀ {b d o}
    → (xs : Num b d o)
    → (ys : Num b d o)
    → (xs! : ¬ (Null xs))
    → (ys! : ¬ (Null ys))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ ys ⟧ ys! > ⟦ xs ⟧ xs!
    → ⟦ ys ⟧ ys! ≥ ⟦ next-number xs xs! ¬max ⟧ next-number-¬Null xs xs! ¬max
next-number-is-LUB {b} {d} {o} xs ys xs! ys! ¬max prop with boundedView b d o
next-number-is-LUB xs ys xs! ys! ¬max prop | IsBounded (Base≡0 d o) = next-number-is-LUB-Base≡0 xs ys xs! ys! ¬max prop
next-number-is-LUB xs ys xs! ys! ¬max prop | IsBounded (HasOnly0 b) = next-number-is-LUB-HasOnly0 xs ys xs! ys! ¬max prop
next-number-is-LUB xs ys xs! ys! ¬max prop | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-is-LUB-d+o≥2 xs ys xs! ys! ¬max d+o≥2 prop
next-number-is-LUB xs ys xs! ys! ¬max prop | IsntBounded (HasNoDigit b o) = next-number-is-LUB-HasNoDigit xs ys xs! ys! ¬max prop

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
