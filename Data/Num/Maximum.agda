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
next-number-Base≡0 {d} {o} xs xs! ¬max  with Base≡0-view d o
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
--
-- -- next-number-Digit+Offset≥2-lemma-2 : ∀ {b d o}
-- --     → (x : Digit (suc d))
-- --     → (x' : Digit (suc d)) (xs : Num (suc b) (suc d) o)
-- --     → (¬Maximum : ¬ (Maximum x (x' ∷ xs)))
-- --     → (greatest : Greatest x)
-- --     → suc d + o ≥ 2
-- --     → ¬ (Maximum x' xs)
-- -- next-number-Digit+Offset≥2-lemma-2 {b} {d} {o} x x' xs ¬max greatest d+o≥2 claim = contradiction p {! ¬p  !}
-- --     where   p : ⟦ x' ∷ xs ⟧ ≥ ⟦ x ∷ (x' ∷ xs) ⟧
-- --             p = claim x (x' ∷ xs)
-- --             ¬p : ⟦ x' ∷ xs ⟧ ≱ ⟦ x ∷ (x' ∷ xs) ⟧
-- --             ¬p = <⇒≱ $
-- --                 start
-- --                     suc ⟦ x' ∷ xs ⟧
-- --                 ≈⟨ cong suc (sym (*-right-identity ⟦ x' ∷ xs ⟧)) ⟩
-- --                     suc (⟦ x' ∷ xs ⟧ * 1)
-- --                 ≤⟨ s≤s (n*-mono ⟦ x' ∷ xs ⟧ (s≤s z≤n)) ⟩
-- --                     suc (⟦ x' ∷ xs ⟧ * suc b)
-- --                 ≤⟨ +n-mono (⟦ x' ∷ xs ⟧ * suc b) (≤-pred d+o≥2) ⟩
-- --                     d + o + ⟦ x' ∷ xs ⟧ * suc b
-- --                 ≈⟨ cong (λ w → w + ⟦ x' ∷ xs ⟧ * suc b) (sym (toℕ-greatest x greatest)) ⟩
-- --                     Digit-toℕ x o + ⟦ x' ∷ xs ⟧ * suc b
-- --                 □
-- -- --
-- --

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
            next! = next-number-d+o≥2-¬Null xs xs! ¬max d+o≥2
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
            next! = next-number-d+o≥2-¬Null xs xs! ¬max d+o≥2
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
        let prop2 : (1 ⊔ o) * suc b > 0
            prop2 = m≤m⊔n 1 o *-mono s≤s z≤n
        in  digit+1-n x greatest ((1 ⊔ o) * suc b) prop2 ∷ 1⊔o d o prop ∷ ∙
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
            next! = next-number-d+o≥2-¬Null (x' ∷ xs) id ¬max prop
            gap = (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) * suc b
            gap>0 = (start
                    1
                ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ x' ∷ xs ⟧))) ⟩
                    suc (⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧)
                ≈⟨ sym (+-∸-assoc 1 {⟦ x' ∷ xs ⟧} ≤-refl) ⟩
                    suc ⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧
                ≤⟨ ∸-mono {suc ⟦ x' ∷ xs ⟧} {⟦ next ⟧ next!} {⟦ x' ∷ xs ⟧} (next-number-d+o≥2-is-greater (x' ∷ xs) id ¬max prop) ≤-refl ⟩
                    ⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧
                □) *-mono (s≤s {0} {b} z≤n)
        in digit+1-n x greatest gap gap>0 ∷ next
    next-number-d+o≥2 {b} {d} {o} (x ∷ xs)      xs! ¬max prop | no ¬greatest
        = digit+1 x ¬greatest ∷ xs

    -- properties of the actual function
    next-number-d+o≥2-¬Null : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (xs! : ¬ (Null xs))
        → (¬max : ¬ (Maximum xs xs!))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → ¬ Null (next-number-d+o≥2 xs xs! ¬max d+o≥2)
    next-number-d+o≥2-¬Null {b} {d} {o} ∙ xs! ¬max prop = contradiction tt xs!
    next-number-d+o≥2-¬Null {b} {d} {o} (x ∷ xs)      xs! ¬max prop with Greatest? x
    next-number-d+o≥2-¬Null {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest with suc d ≤? (1 ⊔ o) * suc b
    next-number-d+o≥2-¬Null {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | yes gapped = id
    next-number-d+o≥2-¬Null {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | no ¬gapped = id
    next-number-d+o≥2-¬Null {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest with Gapped? (x' ∷ xs) id prop
    next-number-d+o≥2-¬Null {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | yes gapped = id
    next-number-d+o≥2-¬Null {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | no ¬gapped = id
    next-number-d+o≥2-¬Null {b} {d} {o} (x ∷ xs)      xs! ¬max prop | no ¬greatest = id
    -- next-number-d+o≥2-¬Null {b} {d} {o} (x ∷ xs)       xs! ¬max prop | no ¬greatest = {!   !}

    Digit-toℕ-1⊔o : ∀ b {d o}
        → (xs : Num (suc b) (suc d) o)
        → (xs! : ¬ (Null xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → 1 ⊔ o ≡ Digit-toℕ (1⊔o d o d+o≥2) o
    Digit-toℕ-1⊔o b {d} {o} xs xs! d+o≥2 = sym (Digit-toℕ-fromℕ {d} {o} (1 ⊔ o) upper-bound lower-bound)
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

    next-number-d+o≥2-is-greater : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (xs! : ¬ (Null xs))
        → (¬max : ¬ (Maximum xs xs!))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → ⟦ next-number-d+o≥2 xs xs! ¬max d+o≥2 ⟧ next-number-d+o≥2-¬Null xs xs! ¬max d+o≥2 > ⟦ xs ⟧ xs!
    next-number-d+o≥2-is-greater {b} {d} {o} ∙ xs! ¬max prop = contradiction tt xs!
    next-number-d+o≥2-is-greater {b} {d} {o} (x ∷ xs)      xs! ¬max prop with Greatest? x
    next-number-d+o≥2-is-greater {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest with suc d ≤? (1 ⊔ o) * suc b
    next-number-d+o≥2-is-greater {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | yes gapped =
        start
            suc (Fin.toℕ x + o)
        ≈⟨ cong (λ w → w + o) greatest ⟩
            suc d + o
        ≈⟨ +-comm (suc d) o ⟩
            o + suc d
        ≤⟨ n+-mono o gapped ⟩
            o + (suc zero ⊔ o) * suc b
        ≈⟨ cong (λ w → o + w * suc b) (Digit-toℕ-1⊔o (suc b) (x ∷ ∙) id prop) ⟩
            o + (Digit-toℕ (1⊔o d o prop) o) * suc b
        □
    next-number-d+o≥2-is-greater {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | yes greatest | no ¬gapped =
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
        ≈⟨ cong (λ w → suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + w * suc b) (Digit-toℕ-1⊔o o (x ∷ ∙) id prop) ⟩
            suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + (Digit-toℕ (1⊔o d o prop) o) * suc b
        ≈⟨ cong (λ w → w + (Digit-toℕ (1⊔o d o prop) o) * suc b) (sym (Digit-toℕ-digit+1-n x greatest ((1 ⊔ o) * suc b) upper-bound lower-bound)) ⟩
            Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) upper-bound) o + (Digit-toℕ (1⊔o d o prop) o) * suc b
        □
    next-number-d+o≥2-is-greater {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest with Gapped? (x' ∷ xs) id prop
    next-number-d+o≥2-is-greater {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | yes gapped =
    -- suc (Fin.toℕ x + o + (⟦ x' ∷ xs ⟧ xs!) * suc b) ≤ ⟦ z ∷ next ⟧ id
        let
            ¬max = next-number-¬Maximum (x' ∷ xs) id prop
            next  = next-number-d+o≥2 (x' ∷ xs) id ¬max prop
            next! = next-number-d+o≥2-¬Null (x' ∷ xs) id ¬max prop

            next>this = ≤-pred $ ≤-step $ next-number-d+o≥2-is-greater (x' ∷ xs) id ¬max prop
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
    next-number-d+o≥2-is-greater {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | yes greatest | no ¬gapped =
    -- suc (Fin.toℕ x + o + (⟦ x' ∷ xs ⟧ xs!) * suc b) ≤ ⟦ digit+1-n x greatest gap gap>0 ∷ next-xs ⟧ id
        let
            ¬max = next-number-¬Maximum (x' ∷ xs) id prop
            next = next-number-d+o≥2 (x' ∷ xs) id ¬max prop
            next! = next-number-d+o≥2-¬Null (x' ∷ xs) id ¬max prop
            gap = (⟦ next ⟧ next! ∸ ⟦ x' ∷ xs ⟧) * suc b
            gap>0 = (start
                    1
                ≤⟨ s≤s (reflexive (sym (n∸n≡0 ⟦ x' ∷ xs ⟧))) ⟩
                    suc (⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧)
                ≈⟨ sym (+-∸-assoc 1 {⟦ x' ∷ xs ⟧} ≤-refl) ⟩
                    suc ⟦ x' ∷ xs ⟧ ∸ ⟦ x' ∷ xs ⟧
                ≤⟨ ∸-mono {suc ⟦ x' ∷ xs ⟧} {⟦ next ⟧ next!} {⟦ x' ∷ xs ⟧} (next-number-d+o≥2-is-greater (x' ∷ xs) id ¬max prop) ≤-refl ⟩
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
            next>this = ≤-pred $ ≤-step $ next-number-d+o≥2-is-greater (x' ∷ xs) id ¬max prop

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
    next-number-d+o≥2-is-greater {b} {d} {o} (x ∷ ∙)       xs! ¬max prop | no ¬greatest
        = reflexive $ sym (Digit-toℕ-digit+1 x ¬greatest)
    next-number-d+o≥2-is-greater {b} {d} {o} (x ∷ x' ∷ xs) xs! ¬max prop | no ¬greatest =
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
next-number-HasNoDigit ∙         xs! ¬max = contradiction tt xs!
next-number-HasNoDigit (() ∷ xs) xs! ¬max


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

next-number-Base≡0-¬Null : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ¬ Null (next-number-Base≡0 xs xs! ¬max)
next-number-Base≡0-¬Null {d} {o} xs xs! ¬max with Base≡0-view d o
next-number-Base≡0-¬Null xs       xs! ¬max | HasOnly0 = contradiction (HasOnly0-Maximum xs xs!) ¬max
next-number-Base≡0-¬Null ∙        xs! ¬max | Others bound = contradiction tt xs!
next-number-Base≡0-¬Null (x ∷ xs) xs! ¬max | Others bound with Greatest? x
next-number-Base≡0-¬Null (x ∷ xs) xs! ¬max | Others bound | yes greatest = contradiction (Base≡0-Maximum x xs greatest) ¬max
next-number-Base≡0-¬Null (x ∷ xs) xs! ¬max | Others bound | no ¬greatest = id

next-number-HasOnly0-¬Null : ∀ {b}
    → (xs : Num (suc b) 1 0)
    → (xs! : ¬ (Null xs))
    → (¬max : ¬ (Maximum xs xs!))
    → ¬ Null (next-number-HasOnly0 xs xs! ¬max)
next-number-HasOnly0-¬Null {b} xs xs! ¬max = contradiction (HasOnly0-Maximum xs xs!) ¬max


next-number-is-LUB-Base≡0 : ∀ {d o}
    → (xs : Num 0 (suc d) o)
    → (ys : Num 0 (suc d) o)
    → (xs! : ¬ (Null xs))
    → (ys! : ¬ (Null ys))
    → (¬max : ¬ (Maximum xs xs!))
    → ⟦ ys ⟧ ys! > ⟦ xs ⟧ xs!
    → ⟦ ys ⟧ ys! ≥ ⟦ next-number-Base≡0 xs xs! ¬max ⟧ next-number-Base≡0-¬Null xs xs! ¬max
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
    → ⟦ ys ⟧ ys! ≥ ⟦ next-number-HasOnly0 xs xs! ¬max ⟧ next-number-HasOnly0-¬Null xs xs! ¬max
    → ¬ Null (next-number-HasOnly0 xs xs! ¬max)
next-number-is-LUB-HasOnly0 {b} xs ys xs! ys! ¬max prop = contradiction (HasOnly0-Maximum xs xs!) ¬max
    --
--
-- next-number-is-LUB-Base≡0 : ∀ {d o}
--     → (xs : Num 0 (suc d) o)
--     → (ys : Num 0 (suc d) o)
--     → (xs! : ¬ (Null xs))
--     → (ys! : ¬ (Null ys))
--     → (¬max : ¬ (Maximum xs xs!))
--     → ⟦ ys ⟧ ys! > ⟦ xs ⟧ xs!
--     → ⟦ ys ⟧ ys! ≥ ⟦ next-number-Base≡0 xs xs! ¬max ⟧ next-number-Base≡0-¬Null xs xs! ¬max

    -- start
    --     Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ xs! * 0
    -- ≤⟨ +n-mono (⟦ xs ⟧ xs! * 0oℕ xs * 0) (reflexive (Digit-toℕ-digit+1 x ¬greatest)) ⟩
    --     suc ⟦ x ∷ xs ⟧
    -- ≤⟨ prop ⟩
    --     ⟦ y ∷ ys ⟧
    -- □
--
-- next-number-is-LUB-Base≡0 : ∀ {d o}
--     → (xs : Num 0 (suc d) o)
--     → (ys : Num 0 (suc d) o)
--     → (¬max : ¬ (Maximum xs))
--     → toℕ ys > toℕ xs
--     → toℕ ys ≥ toℕ (next-number-Base≡0 xs ¬max)
-- next-number-is-LUB-Base≡0 {d} {o} xs ys ¬max prop with Base≡0-view d o
-- next-number-is-LUB-Base≡0 {0} {0} xs ys ¬max prop | HasOnly0 = contradiction (next-number-Base≡0-lemma-1 zero zero xs (s≤s z≤n)) ¬max
-- next-number-is-LUB-Base≡0         ∙  ∙  ¬max ()   | Others bound
-- next-number-is-LUB-Base≡0 {d} {0} ∙ (y ∷ ys) ¬max prop | Others bound =
--     start
--         Digit-toℕ (Digit-fromℕ {d} 1 0 bound) 0 + 0
--     ≤⟨ +n-mono 0 (reflexive (Digit-toℕ-fromℕ {d} {0} (suc zero) bound z≤n)) ⟩
--         1
--     ≤⟨ prop ⟩
--         Fin.toℕ y + 0 + toℕ ys * 0
--     □
-- next-number-is-LUB-Base≡0 {d} {suc o} ∙ (y ∷ ys) ¬max prop | Others bound =
--     start
--         Digit-toℕ (Digit-fromℕ (suc o) (suc o) bound) (suc o) + 0
--     ≤⟨ +n-mono 0 (reflexive (Digit-toℕ-fromℕ {d} (suc o) bound ≤-refl)) ⟩
--         suc o + 0
--     ≤⟨ +n-mono 0 (m≤n+m (suc o) (Fin.toℕ y)) ⟩
--         Digit-toℕ y (suc o) + zero
--     ≤⟨ reflexive (cong (λ w → Digit-toℕ y (suc o) + w) (sym (*-right-zero (toℕ ys)))) ⟩
--         Digit-toℕ y (suc o) + toℕ ys * zero
--     □
-- next-number-is-LUB-Base≡0 (x ∷ xs) ∙        ¬max ()   | Others bound
-- next-number-is-LUB-Base≡0 {d} {o} (x ∷ xs) (y ∷ ys) ¬max prop | Others bound with Greatest? x
-- next-number-is-LUB-Base≡0 {d} {o} (x ∷ xs) (y ∷ ys) ¬max prop | Others bound | yes greatest = contradiction (Base≡0-Maximum x xs greatest) ¬max
-- next-number-is-LUB-Base≡0 {d} {o} (x ∷ xs) (y ∷ ys) ¬max prop | Others bound | no ¬greatest =
--     start
--         Digit-toℕ (digit+1 x ¬greatest) o + toℕ xs * 0
--     ≤⟨ +n-mono (toℕ xs * 0) (reflexive (Digit-toℕ-digit+1 x ¬greatest)) ⟩
--         suc (toℕ (x ∷ xs))
--     ≤⟨ prop ⟩
--         toℕ (y ∷ ys)
--     □
--
--
--
--
-- next-number-is-LUB-HasNoDigit : ∀ {b o}
--     → (xs : Num b 0 o)
--     → (ys : Num b 0 o)
--     → (¬max : ¬ (Maximum xs))
--     → toℕ ys ≥ toℕ (next-number-HasNoDigit xs ¬max)
-- next-number-is-LUB-HasNoDigit {b} {o} ∙         ys ¬max = contradiction (HasNoDigit-lemma b o) ¬max
-- next-number-is-LUB-HasNoDigit         (() ∷ xs) ys ¬max
--
-- next-number-is-LUB-Digit+Offset≥2 : ∀ {b d o}
--     → (xs : Num (suc b) (suc d) o)
--     → (ys : Num (suc b) (suc d) o)
--     → (¬max : ¬ (Maximum xs))
--     → (d+o≥2 : 2 ≤ suc (d + o))
--     → toℕ ys > toℕ xs
--     → toℕ ys ≥ toℕ (next-number-Digit+Offset≥2 xs ¬max d+o≥2)
-- next-number-is-LUB-Digit+Offset≥2 ∙ ∙ ¬max d+o≥2 ()
-- next-number-is-LUB-Digit+Offset≥2 {b} {d} {zero} ∙ (y ∷ ys) ¬max d+o≥2 prop =
--     start
--         Digit-toℕ (Digit-fromℕ {d} (suc zero) zero (≤-pred d+o≥2)) 0 + 0
--     ≤⟨ +n-mono 0 (reflexive (Digit-toℕ-fromℕ {d} 1 (≤-pred d+o≥2) z≤n)) ⟩
--         suc zero
--     ≤⟨ prop ⟩
--         toℕ (y ∷ ys)
--     □
-- next-number-is-LUB-Digit+Offset≥2 {b} {d} {suc o} ∙ (y ∷ ys) ¬max d+o≥2 prop =
--     start
--         Digit-toℕ (Digit-fromℕ {d} (suc o) (suc o) (next-number-1⊔o-upper-bound d (suc o) d+o≥2)) (suc o) + zero
--     ≤⟨ +n-mono 0 (reflexive (Digit-toℕ-fromℕ {d} {suc o} (suc o) (m≤n+m (suc o) d) ≤-refl)) ⟩
--         suc o + 0
--     ≤⟨ (m≤n+m (suc o) (Fin.toℕ y)) +-mono z≤n ⟩
--         Digit-toℕ y (suc o) + toℕ ys * suc b
--     ≤⟨ ≤-refl ⟩
--         toℕ (y ∷ ys)
--     □
-- next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) ∙ ¬max d+o≥2 ()
-- next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop with Greatest? x
-- next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | yes greatest
--     with suc d ≤? (toℕ (next-number-Digit+Offset≥2 xs (next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest d+o≥2) d+o≥2) ∸ toℕ xs) * suc b
-- next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | yes greatest | yes gapped =
--     let
--         ¬max-xs : ¬ (Maximum xs)
--         ¬max-xs = next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest d+o≥2
--
--         next-xs : Num (suc b) (suc d) o
--         next-xs = next-number-Digit+Offset≥2 xs ¬max-xs d+o≥2
--
--         ⟦ys⟧>⟦xs⟧ : toℕ ys > toℕ xs
--         ⟦ys⟧>⟦xs⟧ = tail-mono-strict x y xs ys greatest prop
--
--         ⟦ys⟧≥⟦next-xs⟧ : toℕ ys ≥ toℕ next-xs
--         ⟦ys⟧≥⟦next-xs⟧ = next-number-is-LUB-Digit+Offset≥2 xs ys ¬max-xs d+o≥2 ⟦ys⟧>⟦xs⟧
--     in
--     start
--         toℕ (z ∷ next-xs)
--     ≤⟨ ≤-refl ⟩
--         o + toℕ next-xs * suc b
--     ≤⟨ m≤n+m o (Fin.toℕ y) +-mono (*n-mono (suc b) ⟦ys⟧≥⟦next-xs⟧) ⟩
--         Digit-toℕ y o + toℕ ys * suc b
--     ≤⟨ ≤-refl ⟩
--         toℕ (y ∷ ys)
--     □
--
-- next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | yes greatest | no ¬gapped =
--     let
--
--         ¬max-xs : ¬ (Maximum xs)
--         ¬max-xs = next-number-Digit+Offset≥2-lemma-2 x xs ¬max greatest d+o≥2
--
--         next-xs : Num (suc b) (suc d) o
--         next-xs = next-number-Digit+Offset≥2 xs ¬max-xs d+o≥2
--
--         gap : ℕ
--         gap = (toℕ next-xs ∸ toℕ xs) * suc b
--
--         gap>0 : gap > 0
--         gap>0 = (start
--                 1
--             ≤⟨ s≤s (reflexive (sym (n∸n≡0 (toℕ xs)))) ⟩
--                 suc (toℕ xs ∸ toℕ xs)
--             ≤⟨ reflexive (sym (+-∸-assoc 1 {toℕ xs} ≤-refl)) ⟩
--                 suc (toℕ xs) ∸ toℕ xs
--             ≤⟨ ∸-mono {suc (toℕ xs)} {toℕ next-xs} {toℕ xs} (next-number-is-greater-Digit+Offset≥2 xs ¬max-xs d+o≥2) ≤-refl ⟩
--                 toℕ next-xs ∸ toℕ xs
--             □) *-mono (s≤s z≤n)
--
--         next-xs>xs : toℕ next-xs > toℕ xs
--         next-xs>xs = next-number-is-greater-Digit+Offset≥2 xs ¬max-xs d+o≥2
--
--         next-xs-upper-bound : toℕ next-xs * suc b ∸ toℕ xs * suc b ≤ suc (Digit-toℕ x o)
--         next-xs-upper-bound =
--             start
--                 toℕ next-xs * suc b ∸ toℕ xs * suc b
--             ≤⟨ reflexive (sym (*-distrib-∸ʳ (suc b) (toℕ next-xs) (toℕ xs))) ⟩
--                 (toℕ next-xs ∸ toℕ xs) * suc b
--             ≤⟨ ≤-pred (≰⇒> ¬gapped) ⟩
--                 d
--             ≤⟨ m≤m+n d (suc o) ⟩
--                 d + suc o
--             ≤⟨ reflexive (+-suc d o) ⟩
--                 suc (d + o)
--             ≤⟨ s≤s $ reflexive (sym (toℕ-greatest x greatest)) ⟩
--                 suc (Fin.toℕ x + o)
--             □
--         next-xs-lower-bound : toℕ xs * suc b ≤ toℕ next-xs * suc b
--         next-xs-lower-bound = *n-mono (suc b) (≤-pred (≤-step (next-number-is-greater-Digit+Offset≥2 xs ¬max-xs d+o≥2)))
--
--     in start
--         Digit-toℕ (digit+1-n x greatest gap gap>0 ) o + toℕ next-xs * suc b
--     ≤⟨ +n-mono (toℕ next-xs * suc b) (reflexive (Digit-toℕ-digit+1-n x greatest gap gap>0 (≤-pred $ ≤-step $ ≰⇒> ¬gapped))) ⟩
--         suc (Digit-toℕ x o) ∸ gap + toℕ next-xs * suc b
--     ≤⟨ reflexive (cong (λ w → suc (Digit-toℕ x o) ∸ w + toℕ next-xs * suc b) (*-distrib-∸ʳ (suc b) (toℕ next-xs) (toℕ xs))) ⟩
--         suc (Digit-toℕ x o) ∸ (toℕ next-xs * suc b ∸ toℕ xs * suc b) + toℕ next-xs * suc b
--     ≤⟨ reflexive (m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (toℕ xs * suc b) (toℕ next-xs * suc b) next-xs-lower-bound next-xs-upper-bound) ⟩
--         suc (Digit-toℕ x o) +  toℕ xs * suc b
--     ≤⟨ prop ⟩
--         toℕ (y ∷ ys)
--     □
--
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
-- next-number-is-LUB-Digit+Offset≥2 {b} {d} {o} (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | no ¬greatest =
--     start
--         toℕ (digit+1 x ¬greatest ∷ xs)
--     ≤⟨ ≤-refl ⟩
--         Digit-toℕ (digit+1 x ¬greatest) o + toℕ xs * suc b
--     ≤⟨ +n-mono (toℕ xs * suc b) (reflexive (Digit-toℕ-digit+1 x ¬greatest)) ⟩
--         suc (Fin.toℕ x + o + toℕ xs * suc b)
--     ≤⟨ prop ⟩
--         Fin.toℕ y + o + toℕ ys * suc b
--     ≤⟨ ≤-refl ⟩
--         toℕ (y ∷ ys)
--     □
--
-- next-number-is-LUB : ∀ {b d o}
--     → (xs : Num b d o)
--     → (ys : Num b d o)
--     → (¬max : ¬ (Maximum xs))
--     → toℕ ys > toℕ xs
--     → toℕ ys ≥ toℕ (next-number xs ¬max)
-- next-number-is-LUB {b} {d} {o} xs ys ¬max prop with boundedView b d o
-- next-number-is-LUB xs ys ¬max prop | IsBounded (Base≡0 d o) = next-number-is-LUB-Base≡0 xs ys ¬max prop
-- next-number-is-LUB xs ys ¬max prop | IsBounded (HasNoDigit b o) = next-number-is-LUB-HasNoDigit xs ys ¬max
-- next-number-is-LUB xs ys ¬max prop | IsBounded (HasOnly0 b) = contradiction (HasOnly0-Maximum (suc b) xs) ¬max
-- next-number-is-LUB xs ys ¬max prop | IsntBounded (Digit+Offset≥2 b d o d+o≥2) = next-number-is-LUB-Digit+Offset≥2 xs ys ¬max d+o≥2 prop
