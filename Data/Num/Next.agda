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

-- 1 `max` o, in case that the least digit "o" is 0, which is too small
1⊔o : ∀ d o → 2 ≤ suc (d + o) → Digit (suc d)
1⊔o d o d+o≥2 = Digit-fromℕ (1 ⊔ o) o (next-number-1⊔o-upper-bound d o d+o≥2)

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



mutual

    Abundant : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Set
    Abundant {b} {d} {o} (x ∙)    _     = (1 ⊔ o)                * suc b ≤ suc d
    Abundant {b} {d} {o} (x ∷ xs) d+o≥2 = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b ≤ suc d
        where
            ¬max-xs : ¬ (Maximum xs)
            ¬max-xs = Maximum-Others xs d+o≥2

            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Others xs ¬max-xs d+o≥2

    Abundant? : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Dec (Abundant {b} {d} {o} xs d+o≥2)
    Abundant? {b} {d} {o} (x ∙)    _     = (1 ⊔ o)                * suc b ≤? suc d
    Abundant? {b} {d} {o} (x ∷ xs) d+o≥2 = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b ≤? suc d
        where
            ¬max-xs : ¬ (Maximum xs)
            ¬max-xs = Maximum-Others xs d+o≥2

            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Others xs ¬max-xs d+o≥2


    data OthersView : (b d o : ℕ) (xs : Num b d o) (d+o≥2 : 2 ≤ d + o) → Set where
        NeedNoCarry : ∀ b d o
            → {xs : Num (suc b) (suc d) o}
            → {d+o≥2 : 2 ≤ suc (d + o)}
            → (¬greatest : ¬ (Greatest (lsd xs)))
            → OthersView (suc b) (suc d) o xs d+o≥2
        Gapped : ∀ b d o
            → {xs : Num (suc b) (suc d) o}
            → {d+o≥2 : 2 ≤ suc (d + o)}
            → (greatest : Greatest (lsd xs))
            → (¬abundant : ¬ (Abundant xs d+o≥2))
            → OthersView (suc b) (suc d) o xs d+o≥2
        ¬Gapped : ∀ b d o
            → {xs : Num (suc b) (suc d) o}
            → {d+o≥2 : 2 ≤ suc (d + o)}
            → (greatest : Greatest (lsd xs))
            → (abundant : Abundant xs d+o≥2)
            → OthersView (suc b) (suc d) o xs d+o≥2

    othersView : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → ¬ (Maximum xs)
        → (d+o≥2 : 2 ≤ suc (d + o))
        → OthersView (suc b) (suc d) o xs d+o≥2
    othersView {b} {d} {o} xs ¬max d+o≥2 with Greatest? (lsd xs)
    othersView {b} {d} {o} xs ¬max d+o≥2 | yes greatest with Abundant? xs d+o≥2
    othersView {b} {d} {o} xs ¬max d+o≥2 | yes greatest | yes abundant = ¬Gapped b d o greatest abundant
    othersView {b} {d} {o} xs ¬max d+o≥2 | yes greatest | no ¬abundant = Gapped b d o greatest ¬abundant
    othersView {b} {d} {o} xs ¬max d+o≥2 | no ¬greatest = NeedNoCarry b d o ¬greatest

    next-number-Others : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (¬max : ¬ (Maximum xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → Num (suc b) (suc d) o
    next-number-Others xs ¬max d+o≥2 with othersView xs ¬max d+o≥2
    next-number-Others (x ∙)    ¬max d+o≥2 | NeedNoCarry b d o ¬greatest
        = digit+1 x ¬greatest ∙
    next-number-Others (x ∷ xs) ¬max d+o≥2 | NeedNoCarry b d o ¬greatest
        = digit+1 x ¬greatest ∷ xs
    next-number-Others (x ∙)    ¬max d+o≥2 | Gapped b d o greatest ¬abundant
        = z ∷ 1⊔o d o d+o≥2 ∙
    next-number-Others (x ∷ xs) ¬max d+o≥2 | Gapped b d o greatest ¬abundant
        = z ∷ next-xs
        where
            ¬max-xs : ¬ (Maximum xs)
            ¬max-xs = Maximum-Others xs d+o≥2

            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Others xs ¬max-xs d+o≥2
    next-number-Others (x ∙)    ¬max d+o≥2 | ¬Gapped b d o greatest abundant
        = digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ 1⊔o d o d+o≥2 ∙
        where
            lower-bound : (1 ⊔ o) * suc b > 0
            lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n

    next-number-Others (x ∷ xs) ¬max d+o≥2 | ¬Gapped b d o greatest abundant
        = digit+1-n x greatest gap lower-bound ∷ next-xs
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
            upper-bound = abundant



    next-number-is-greater-Others : ∀ {b d o}
        → (xs : Num (suc b) (suc d) o)
        → (¬max : ¬ (Maximum xs))
        → (d+o≥2 : 2 ≤ suc (d + o))
        → ⟦ next-number-Others xs ¬max d+o≥2 ⟧ > ⟦ xs ⟧
    next-number-is-greater-Others xs ¬max d+o≥2 with othersView xs ¬max d+o≥2
    next-number-is-greater-Others (x ∙) ¬max d+o≥2 | NeedNoCarry b d o ¬greatest
        = reflexive $ sym (Digit-toℕ-digit+1 x ¬greatest)
    next-number-is-greater-Others (x ∷ xs) ¬max d+o≥2 | NeedNoCarry b d o ¬greatest
        = reflexive $ cong (λ w → w + ⟦ xs ⟧ * suc b) (sym (Digit-toℕ-digit+1 x ¬greatest))
    next-number-is-greater-Others (x ∙) ¬max d+o≥2 | Gapped b d o greatest ¬abundant =
        start
            suc (Fin.toℕ x + o)
        ≈⟨ cong (λ w → w + o) greatest ⟩
            suc d + o
        ≈⟨ +-comm (suc d) o ⟩
            o + suc d
        ≤⟨ n+-mono o (<⇒≤ (≰⇒> ¬abundant)) ⟩
            o + (suc zero ⊔ o) * suc b
        ≈⟨ cong (λ w → o + w * suc b) (sym (Digit-toℕ-1⊔o d o d+o≥2)) ⟩
            o + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
        □
    next-number-is-greater-Others (x ∷ xs) ¬max d+o≥2 | Gapped b d o greatest ¬abundant =
        start
            suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
        ≈⟨ cong (λ w → suc w + ⟦ xs ⟧ * suc b) (toℕ-greatest x greatest) ⟩
            suc d + o + ⟦ xs ⟧ * suc b
        ≈⟨ +-assoc (suc d) o (⟦ xs ⟧ * suc b) ⟩
            suc d + (o + ⟦ xs ⟧ * suc b)
        ≈⟨ a+[b+c]≡b+[a+c] (suc d) o (⟦ xs ⟧ * suc b) ⟩
            o + (suc d + ⟦ xs ⟧ * suc b)
        ≤⟨ n+-mono o (+n-mono (⟦ xs ⟧ * suc b) (<⇒≤ (≰⇒> ¬abundant))) ⟩
            o + ((⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b + ⟦ xs ⟧ * suc b)
        ≈⟨ cong (λ w → o + w) (sym (distribʳ-*-+ (suc b) (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) ⟦ xs ⟧)) ⟩
            o + (⟦ next-xs ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧) * suc b
        ≈⟨ cong (λ w → o + w * suc b) (m∸n+n≡m (<⇒≤ next-xs>xs)) ⟩
            o + ⟦ next-xs ⟧ * suc b
        ≈⟨ refl ⟩
            ⟦ z ∷ next-xs ⟧
        □
        where
            ¬max-xs : ¬ (Maximum xs)
            ¬max-xs = Maximum-Others xs d+o≥2

            next-xs : Num (suc b) (suc d) o
            next-xs = next-number-Others xs ¬max-xs d+o≥2

            next-xs>xs : ⟦ next-xs ⟧ > ⟦ xs ⟧
            next-xs>xs = next-number-is-greater-Others xs ¬max-xs d+o≥2

    next-number-is-greater-Others (x ∙) ¬max d+o≥2 | ¬Gapped b d o greatest abundant =
        start
            suc (Fin.toℕ x + o)
        ≈⟨ sym (m∸n+n≡m {_} {(suc zero ⊔ o) * suc b} upper-bound') ⟩
            suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + (suc zero ⊔ o) * suc b
        ≈⟨ cong (λ w → suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + w * suc b) (sym (Digit-toℕ-1⊔o d o d+o≥2)) ⟩
            suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
        ≈⟨ cong (λ w → w + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b) (sym (Digit-toℕ-digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound upper-bound)) ⟩
            Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
        □
        where
            upper-bound : (suc zero ⊔ o) * suc b ≤ suc d
            upper-bound = abundant

            lower-bound : 1 ≤ (suc zero ⊔ o) * suc b
            lower-bound = m≤m⊔n (suc zero) o *-mono s≤s z≤n

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
    next-number-is-greater-Others (x ∷ xs) ¬max d+o≥2 | ¬Gapped b d o greatest abundant =
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
            upper-bound = abundant

            next-x : Digit (suc d)
            next-x = digit+1-n x greatest gap lower-bound

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


next-number-is-LUB-Others : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (ys : Num (suc b) (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → (d+o≥2 : 2 ≤ suc (d + o))
    → ⟦ ys ⟧ > ⟦ xs ⟧
    → ⟦ ys ⟧ ≥ ⟦ next-number-Others xs ¬max d+o≥2 ⟧
next-number-is-LUB-Others xs ys ¬max d+o≥2 prop with othersView xs ¬max d+o≥2
next-number-is-LUB-Others (x ∙) ys ¬max d+o≥2 prop | NeedNoCarry b d o ¬greatest =
    start
        Digit-toℕ (digit+1 x ¬greatest) o
    ≈⟨ Digit-toℕ-digit+1 x ¬greatest ⟩
        suc (Digit-toℕ x o)
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □
next-number-is-LUB-Others (x ∷ xs) ys ¬max d+o≥2 prop | NeedNoCarry b d o ¬greatest =
    start
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * suc b
    ≈⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) (Digit-toℕ-digit+1 x ¬greatest) ⟩
        suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □
next-number-is-LUB-Others (x ∙) (y ∙) ¬max d+o≥2 prop | Gapped b d o greatest ¬abundant
    = contradiction prop (>⇒≰ (s≤s (greatest-of-all o x y greatest)))
next-number-is-LUB-Others (x ∙) (y ∷ ys) ¬max d+o≥2 prop | Gapped b d o greatest ¬abundant =
    let
        ⟦ys⟧>0 = tail-mono-strict-Null x y ys greatest prop
    in
    start
        o + (Digit-toℕ (1⊔o d o d+o≥2) o) * suc b
    ≈⟨ cong (λ w → o + w * suc b) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
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


next-number-is-LUB-Others (x ∷ xs) (y ∙) ¬max d+o≥2 prop | Gapped b d o greatest ¬abundant = contradiction prop $ >⇒≰ $
    start
        suc (Fin.toℕ y + o)
    ≤⟨ s≤s (greatest-of-all o x y greatest) ⟩
        suc (Fin.toℕ x + o)
    ≤⟨ m≤m+n (suc (Fin.toℕ x + o)) (⟦ xs ⟧ * suc b) ⟩
        suc (Fin.toℕ x + o + ⟦ xs ⟧ * suc b)
    □
next-number-is-LUB-Others (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | Gapped b d o greatest ¬abundant =
    start
        o + ⟦ next-xs ⟧ * suc b
    ≤⟨ n+-mono o (*n-mono (suc b) ⟦next-xs⟧≤⟦ys⟧) ⟩
        o + ⟦ ys ⟧ * suc b
    ≤⟨ +n-mono (⟦ ys ⟧ * suc b) (m≤n+m o (Fin.toℕ y)) ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □
    where
        ¬max-xs : ¬ (Maximum xs)
        ¬max-xs = Maximum-Others xs d+o≥2

        next-xs : Num (suc b) (suc d) o
        next-xs = next-number-Others xs ¬max-xs d+o≥2

        ⟦xs⟧<⟦ys⟧ : ⟦ xs ⟧ < ⟦ ys ⟧
        ⟦xs⟧<⟦ys⟧ = tail-mono-strict x xs y ys greatest prop

        ⟦next-xs⟧≤⟦ys⟧ : ⟦ next-xs ⟧ ≤ ⟦ ys ⟧
        ⟦next-xs⟧≤⟦ys⟧ = next-number-is-LUB-Others xs ys ¬max-xs d+o≥2 ⟦xs⟧<⟦ys⟧


next-number-is-LUB-Others (x ∙) ys ¬max d+o≥2 prop | ¬Gapped b d o greatest abundant =
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
    where
        upper-bound : (suc zero ⊔ o) * suc b ≤ suc d
        upper-bound = abundant

        lower-bound : 1 ≤ (suc zero ⊔ o) * suc b
        lower-bound = m≤m⊔n (suc zero) o *-mono s≤s z≤n

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
next-number-is-LUB-Others (x ∷ xs) (y ∙) ¬max d+o≥2 prop | ¬Gapped b d o greatest abundant = contradiction prop $ >⇒≰ $
    start
        suc (Fin.toℕ y + o)
    ≤⟨ s≤s (greatest-of-all o x y greatest) ⟩
        suc (Fin.toℕ x + o)
    ≤⟨ m≤m+n (suc (Fin.toℕ x + o)) (⟦ xs ⟧ * suc b) ⟩
        suc (Fin.toℕ x + o + ⟦ xs ⟧ * suc b)
    □
next-number-is-LUB-Others (x ∷ xs) (y ∷ ys) ¬max d+o≥2 prop | ¬Gapped b d o greatest abundant =
    start
        ⟦ digit+1-n x greatest gap lower-bound ∷ next-xs ⟧
    ≈⟨ cong (λ w → w + ⟦ next-xs ⟧ * suc b) (Digit-toℕ-digit+1-n x greatest gap lower-bound upper-bound) ⟩
        suc (Digit-toℕ x o) ∸ gap + ⟦ next-xs ⟧ * suc b
    ≈⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + ⟦ next-xs ⟧ * suc b) (*-distrib-∸ʳ (suc b) ⟦ next-xs ⟧ ⟦ xs ⟧) ⟩
        suc (Digit-toℕ x o) ∸ (⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b) + ⟦ next-xs ⟧ * suc b
    ≈⟨ m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ xs ⟧ * suc b) (⟦ next-xs ⟧ * suc b) (*n-mono (suc b) (<⇒≤ ⟦next-xs⟧>⟦xs⟧)) upper-bound' ⟩
        suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
    ≤⟨ prop ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □
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
        upper-bound = abundant

        next-x : Digit (suc d)
        next-x = digit+1-n x greatest gap lower-bound

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
