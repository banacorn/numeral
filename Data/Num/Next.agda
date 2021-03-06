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

open import Function
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

--------------------------------------------------------------------------------
-- next-numeral: NullBase
--------------------------------------------------------------------------------

next-numeral-NullBase : ∀ {d o}
    → (xs : Numeral 0 (suc d) o)
    → ¬ (Maximum xs)
    → Numeral 0 (suc d) o
next-numeral-NullBase xs       ¬max with Greatest? (lsd xs)
next-numeral-NullBase xs       ¬max | yes greatest =
    contradiction (Maximum-NullBase-Greatest xs greatest) ¬max
next-numeral-NullBase (x ∙)    ¬max | no ¬greatest = digit+1 x ¬greatest ∙
next-numeral-NullBase (x ∷ xs) ¬max | no ¬greatest = digit+1 x ¬greatest ∷ xs

next-numeral-NullBase-lemma : ∀ {d o}
    → (xs : Numeral 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ next-numeral-NullBase xs ¬max ⟧ ≡ suc ⟦ xs ⟧
next-numeral-NullBase-lemma {d} {o} xs    ¬max with Greatest? (lsd xs)
next-numeral-NullBase-lemma {d} {o} xs    ¬max | yes greatest =
    contradiction (Maximum-NullBase-Greatest xs greatest) ¬max
next-numeral-NullBase-lemma {d} {o} (x ∙) ¬max | no ¬greatest =
    begin
        Digit-toℕ (digit+1 x ¬greatest) o
    ≡⟨ digit+1-toℕ x ¬greatest ⟩
        suc (Fin.toℕ x + o)
    ∎
next-numeral-NullBase-lemma {d} {o} (x ∷ xs) ¬max | no ¬greatest =
    begin
        ⟦ digit+1 x ¬greatest ∷ xs ⟧
    ≡⟨ refl ⟩
        Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * zero
    ≡⟨ cong (λ w → w + ⟦ xs ⟧ * zero) (digit+1-toℕ x ¬greatest) ⟩
        suc (Fin.toℕ x + o + ⟦ xs ⟧ * zero)
    ≡⟨ refl ⟩
        suc ⟦ x ∷ xs ⟧
    ∎

next-numeral-is-greater-NullBase : ∀ {d o}
    → (xs : Numeral 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ next-numeral-NullBase xs ¬max ⟧ > ⟦ xs ⟧
next-numeral-is-greater-NullBase xs ¬max =
    start
        suc ⟦ xs ⟧
    ≈⟨ sym (next-numeral-NullBase-lemma xs ¬max) ⟩
        ⟦ next-numeral-NullBase xs ¬max ⟧
    □

next-numeral-is-immediate-NullBase : ∀ {d o}
    → (xs : Numeral 0 (suc d) o)
    → (ys : Numeral 0 (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ ys ⟧ > ⟦ xs ⟧
    → ⟦ ys ⟧ ≥ ⟦ next-numeral-NullBase xs ¬max ⟧
next-numeral-is-immediate-NullBase xs ys ¬max prop =
    start
        ⟦ next-numeral-NullBase xs ¬max ⟧
    ≈⟨ next-numeral-NullBase-lemma xs ¬max ⟩
        suc ⟦ xs ⟧
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □

--------------------------------------------------------------------------------
-- next-numeral: Proper
--------------------------------------------------------------------------------


mutual
    Gapped#0 : ∀ b d o → Set
    Gapped#0 b d o = suc d < carry o * suc b

    Gapped#N : ∀ b d o
        → (xs : Numeral (suc b) (suc d) o)
        → (proper : 2 ≤ suc (d + o))
        → Set
    Gapped#N b d o xs proper = suc d < (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
        where
            next-xs : Numeral (suc b) (suc d) o
            next-xs = next-numeral-Proper xs proper

    Gapped#0? :  ∀ b d o → Dec (Gapped#0 b d o)
    Gapped#0? b d o = suc (suc d) ≤? carry o * suc b

    Gapped#N? :  ∀ b d o
        → (xs : Numeral (suc b) (suc d) o)
        → (proper : 2 ≤ suc (d + o))
        → Dec (Gapped#N b d o xs proper)
    Gapped#N? b d o xs proper = suc (suc d) ≤? (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
        where
            next-xs : Numeral (suc b) (suc d) o
            next-xs = next-numeral-Proper xs proper

    -- Gap#N
    Gapped : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (proper : 2 ≤ suc (d + o))
        → Set
    Gapped {b} {d} {o} (x ∙)    proper = Gapped#0 b d o
    Gapped {b} {d} {o} (x ∷ xs) proper = Gapped#N b d o xs proper

    Gapped? : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (proper : 2 ≤ suc (d + o))
        → Dec (Gapped {b} {d} {o} xs proper)
    Gapped? {b} {d} {o} (x ∙)    proper = Gapped#0? b d o
    Gapped? {b} {d} {o} (x ∷ xs) proper = Gapped#N? b d o xs proper

    data NextView : (b d o : ℕ) (xs : Numeral b d o) (proper : 2 ≤ d + o) → Set where
        Interval : ∀ b d o
            → {xs : Numeral (suc b) (suc d) o}
            → {proper : 2 ≤ suc (d + o)}
            → (¬greatest : ¬ (Greatest (lsd xs)))
            → NextView (suc b) (suc d) o xs proper
        GappedEndpoint : ∀ b d o
            → {xs : Numeral (suc b) (suc d) o}
            → {proper : 2 ≤ suc (d + o)}
            → (greatest : Greatest (lsd xs))
            → (gapped : Gapped xs proper)
            → NextView (suc b) (suc d) o xs proper
        UngappedEndpoint : ∀ b d o
            → {xs : Numeral (suc b) (suc d) o}
            → {proper : 2 ≤ suc (d + o)}
            → (greatest : Greatest (lsd xs))
            → (¬gapped : ¬ (Gapped xs proper))
            → NextView (suc b) (suc d) o xs proper

    nextView : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (proper : 2 ≤ suc (d + o))
        → NextView (suc b) (suc d) o xs proper
    nextView {b} {d} {o} xs proper with Greatest? (lsd xs)
    nextView {b} {d} {o} xs proper | yes greatest with Gapped? xs proper
    nextView {b} {d} {o} xs proper | yes greatest | yes gapped = GappedEndpoint  b d o greatest gapped
    nextView {b} {d} {o} xs proper | yes greatest | no ¬gapped = UngappedEndpoint b d o greatest ¬gapped
    nextView {b} {d} {o} xs proper | no ¬greatest = Interval b d o ¬greatest

    next-numeral-Proper-Interval : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (¬greatest : ¬ (Greatest (lsd xs)))
        → (proper : 2 ≤ suc (d + o))
        → Numeral (suc b) (suc d) o
    next-numeral-Proper-Interval (x ∙)    ¬greatest proper = digit+1 x ¬greatest ∙
    next-numeral-Proper-Interval (x ∷ xs) ¬greatest proper = digit+1 x ¬greatest ∷ xs

    next-numeral-Proper-GappedEndpoint : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (proper : 2 ≤ suc (d + o))
        → (gapped : Gapped xs proper)
        → Numeral (suc b) (suc d) o
    next-numeral-Proper-GappedEndpoint {b} {d} {o} (x ∙)    proper gapped = z ∷ carry-digit d o proper ∙
    next-numeral-Proper-GappedEndpoint {b} {d} {o} (x ∷ xs) proper gapped = z ∷ next-numeral-Proper xs proper

    next-numeral-Proper-UngappedEndpoint : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (greatest : Greatest (lsd xs))
        → (proper : 2 ≤ suc (d + o))
        → (¬gapped : ¬ (Gapped xs proper))
        → Numeral (suc b) (suc d) o
    next-numeral-Proper-UngappedEndpoint {b} {d} {o} (x ∙) greatest proper gapped
        = digit+1-n x greatest (carry o * suc b) lower-bound ∷ carry-digit d o proper ∙
        where
            lower-bound : carry o * suc b > 0
            lower-bound =
                start
                    1
                ≤⟨ m≤m*1+n 1 b ⟩
                    1 * suc b
                ≤⟨ *n-mono (suc b) (m≤m⊔n 1 o) ⟩
                    carry o * suc b
                □

    next-numeral-Proper-UngappedEndpoint {b} {d} {o} (x ∷ xs) greatest proper gapped
        = digit+1-n x greatest gap lower-bound ∷ next-xs
        where
            next-xs : Numeral (suc b) (suc d) o
            next-xs = next-numeral-Proper xs proper

            gap : ℕ
            gap = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b

            lower-bound : gap > 0
            lower-bound =
                start
                    1
                ≤⟨ m≤m*1+n 1 b ⟩
                    1 * suc b
                ≤⟨ *n-mono (suc b) (m≥n+o⇒m∸o≥n ⟦ next-xs ⟧ 1 ⟦ xs ⟧ (next-numeral-is-greater-Proper xs proper)) ⟩
                    (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
                □


    next-numeral-Proper : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (proper : 2 ≤ suc (d + o))
        → Numeral (suc b) (suc d) o
    next-numeral-Proper xs proper with nextView xs proper
    next-numeral-Proper xs proper | Interval b d o ¬greatest
        = next-numeral-Proper-Interval xs ¬greatest proper
    next-numeral-Proper xs proper | GappedEndpoint b d o greatest gapped
        = next-numeral-Proper-GappedEndpoint xs proper gapped
    next-numeral-Proper xs proper | UngappedEndpoint b d o greatest ¬gapped
        = next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped

    next-numeral-Proper-Interval-lemma : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (¬greatest : ¬ (Greatest (lsd xs)))
        → (proper : 2 ≤ suc (d + o))
        → ⟦ next-numeral-Proper-Interval xs ¬greatest proper ⟧ ≡ suc ⟦ xs ⟧
    next-numeral-Proper-Interval-lemma {b} {d} {o} (x ∙) ¬greatest proper =
        -- ⟦ digit+1 x ¬greatest ∙ ⟧ ≡ suc ⟦ x ∙ ⟧
        begin
            Digit-toℕ (digit+1 x ¬greatest) o
        ≡⟨ digit+1-toℕ x ¬greatest ⟩
            suc (Digit-toℕ x o)
        ∎
    next-numeral-Proper-Interval-lemma {b} {d} {o} (x ∷ xs) ¬greatest proper =
    -- ⟦ digit+1 x ¬greatest ∷ xs ⟧ ≡ suc ⟦ x ∷ xs ⟧
        begin
            Digit-toℕ (digit+1 x ¬greatest) o + ⟦ xs ⟧ * suc b
        ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) (digit+1-toℕ x ¬greatest) ⟩
            suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
        ∎

    next-numeral-Proper-GappedEndpoint-lemma : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (greatest : Greatest (lsd xs))
        → (proper : 2 ≤ suc (d + o))
        → (gapped : Gapped xs proper)
        → ⟦ next-numeral-Proper-GappedEndpoint xs proper gapped ⟧ > suc ⟦ xs ⟧
    next-numeral-Proper-GappedEndpoint-lemma {b} {d} {o} (x ∙) greatest proper gapped =
        -- ⟦ z ∷ carry-digit d o proper ∙ ⟧ > suc ⟦ x ∙ ⟧
        start
            suc (suc (Fin.toℕ x + o))
        ≈⟨ cong (λ w → suc w + o) greatest ⟩
            suc (suc d) + o
        ≈⟨ +-comm (suc (suc d)) o ⟩
            o + suc (suc d)
        ≤⟨ n+-mono o gapped ⟩
            o + carry o * suc b
        ≈⟨ cong (λ w → o + w * suc b) (sym (carry-digit-toℕ d o proper)) ⟩
            o + (Digit-toℕ (carry-digit d o proper) o) * suc b
        □
    next-numeral-Proper-GappedEndpoint-lemma {b} {d} {o} (x ∷ xs) greatest proper gapped
        = proof
        where
            next-xs : Numeral (suc b) (suc d) o
            next-xs = next-numeral-Proper xs proper

            next-xs>xs : ⟦ next-xs ⟧ > ⟦ xs ⟧
            next-xs>xs = next-numeral-is-greater-Proper xs proper

            next : Numeral (suc b) (suc d) o
            next = z ∷ next-xs

            -- ⟦ z ∷ next-numeral-Proper xs (Maximum-Proper xs proper) proper ⟧ > suc ⟦ x ∷ xs ⟧
            proof : ⟦ next ⟧ > suc ⟦ x ∷ xs ⟧
            proof = start
                    suc (suc (Digit-toℕ x o)) + ⟦ xs ⟧ * suc b
                ≈⟨ cong (λ w → suc (suc w) + ⟦ xs ⟧ * suc b) (greatest-digit-toℕ x greatest) ⟩
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

    next-numeral-Proper-UngappedEndpoint-lemma : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (greatest : Greatest (lsd xs))
        → (proper : 2 ≤ suc (d + o))
        → (¬gapped : ¬ (Gapped xs proper))
        → ⟦ next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped ⟧ ≡ suc ⟦ xs ⟧
    next-numeral-Proper-UngappedEndpoint-lemma {b} {d} {o} (x ∙) greatest proper ¬gapped = proof
        -- ⟦ digit+1-n x greatest (carry o * suc b) lower-bound ∷ carry-digit d o proper ∙ ⟧ ≡ suc ⟦ x ∙ ⟧
        where
            lower-bound : carry o * suc b > 0
            lower-bound =
                start
                    1
                ≤⟨ m≤m*1+n 1 b ⟩
                    1 * suc b
                ≤⟨ *n-mono (suc b) (m≤m⊔n 1 o) ⟩
                    carry o * suc b
                □

            upper-bound : carry o * suc b ≤ suc d
            upper-bound = ≤-pred $ ≰⇒> ¬gapped

            upper-bound' : carry o * suc b ≤ suc (Fin.toℕ x + o)
            upper-bound' = start
                    carry o * suc b
                ≤⟨ upper-bound ⟩
                    suc d
                ≈⟨ sym greatest ⟩
                    suc (Fin.toℕ x)
                ≤⟨ m≤m+n (suc (Fin.toℕ x)) o ⟩
                    suc (Fin.toℕ x + o)
                □

            next : Numeral (suc b) (suc d) o
            next = digit+1-n x greatest (carry o * suc b) lower-bound ∷ carry-digit d o proper ∙

            proof : ⟦ next ⟧ ≡ suc (Digit-toℕ x o)
            proof =
                begin
                    Digit-toℕ (digit+1-n x greatest (carry o * suc b) lower-bound) o + Digit-toℕ (carry-digit d o proper) o * suc b
                ≡⟨ cong (λ w → Digit-toℕ (digit+1-n x greatest (carry o * suc b) lower-bound) o + w * suc b) (carry-digit-toℕ d o proper) ⟩
                    Digit-toℕ (digit+1-n x greatest (carry o * suc b) lower-bound) o + carry o * suc b
                ≡⟨ cong (λ w → w + carry o * suc b) (digit+1-n-toℕ x greatest (carry o * suc b) lower-bound upper-bound) ⟩
                    suc (Fin.toℕ x + o) ∸ carry o * suc b + carry o * suc b
                ≡⟨ m∸n+n≡m upper-bound' ⟩
                    suc (Digit-toℕ x o)
                ∎
    next-numeral-Proper-UngappedEndpoint-lemma {b} {d} {o} (x ∷ xs) greatest proper ¬gapped = proof
        -- ⟦ digit+1-n x greatest gap gap>0 ∷ next ∙ ⟧ ≡ suc ⟦ x ∷ xs ⟧
        where
            ¬max-xs : ¬ (Maximum xs)
            ¬max-xs = Maximum-Proper xs proper

            next-xs : Numeral (suc b) (suc d) o
            next-xs = next-numeral-Proper xs proper

            lower-bound : (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b > 0
            lower-bound =
                start
                    1
                ≤⟨ m≤m*1+n 1 b ⟩
                    1 * suc b
                ≤⟨ *n-mono (suc b) (m≥n+o⇒m∸o≥n ⟦ next-xs ⟧ 1 ⟦ xs ⟧ (next-numeral-is-greater-Proper xs proper)) ⟩
                    (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
                □

            upper-bound : (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b ≤ suc d
            upper-bound = ≤-pred $ ≰⇒> ¬gapped

            next : Numeral (suc b) (suc d) o
            next = digit+1-n x greatest ((⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b) lower-bound ∷ next-xs

            ⟦next-xs⟧>⟦xs⟧ : ⟦ next-xs ⟧ > ⟦ xs ⟧
            ⟦next-xs⟧>⟦xs⟧ = next-numeral-is-greater-Proper xs proper

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
                ≡⟨ cong (λ w → w + ⟦ next-xs ⟧ * suc b) (digit+1-n-toℕ x greatest ((⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b) lower-bound upper-bound) ⟩
                    suc (Digit-toℕ x o) ∸ (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b + ⟦ next-xs ⟧ * suc b
                ≡⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + ⟦ next-xs ⟧ * suc b) (*-distrib-∸ʳ (suc b) ⟦ next-xs ⟧ ⟦ xs ⟧) ⟩
                    suc (Digit-toℕ x o) ∸ (⟦ next-xs ⟧ * suc b ∸ ⟦ xs ⟧ * suc b) + ⟦ next-xs ⟧ * suc b
                ≡⟨ m∸[o∸n]+o≡m+n (suc (Digit-toℕ x o)) (⟦ xs ⟧ * suc b) (⟦ next-xs ⟧ * suc b) (*n-mono (suc b) (<⇒≤ ⟦next-xs⟧>⟦xs⟧)) upper-bound' ⟩
                    suc ⟦ x ∷ xs ⟧
                ∎

    next-numeral-is-greater-Proper : ∀ {b d o}
        → (xs : Numeral (suc b) (suc d) o)
        → (proper : 2 ≤ suc (d + o))
        → ⟦ next-numeral-Proper xs proper ⟧ > ⟦ xs ⟧
    next-numeral-is-greater-Proper xs proper with nextView xs proper
    next-numeral-is-greater-Proper xs proper | Interval b d o ¬greatest =
        start
            suc ⟦ xs ⟧
        ≈⟨ sym (next-numeral-Proper-Interval-lemma xs ¬greatest proper) ⟩
            ⟦ next-numeral-Proper-Interval xs ¬greatest proper ⟧
        □
    next-numeral-is-greater-Proper xs proper | GappedEndpoint b d o greatest gapped =
        start
            suc ⟦ xs ⟧
        ≤⟨ n≤1+n (suc ⟦ xs ⟧) ⟩
            suc (suc ⟦ xs ⟧)
        ≤⟨ next-numeral-Proper-GappedEndpoint-lemma xs greatest proper gapped ⟩
            ⟦ next-numeral-Proper-GappedEndpoint xs proper gapped ⟧
        □
    next-numeral-is-greater-Proper xs proper | UngappedEndpoint b d o greatest ¬gapped =
        start
            suc ⟦ xs ⟧
        ≈⟨ sym (next-numeral-Proper-UngappedEndpoint-lemma xs greatest proper ¬gapped) ⟩
            ⟦ next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped ⟧
        □

-- gap : ∀ {b d o}
--     → (xs : Numeral (suc b) (suc d) o)
--     → (proper : 2 ≤ suc (d + o))
--     → ℕ
-- gap {b} {d} {o} (x ∙)    proper = carry o                * suc b
-- gap {b} {d} {o} (x ∷ xs) proper = (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
--     where
--         next-xs : Numeral (suc b) (suc d) o
--         next-xs = next-numeral-Proper xs proper
--
-- gap>0 : ∀ {b d o}
--     → (xs : Numeral (suc b) (suc d) o)
--     → (proper : 2 ≤ suc (d + o))
--     → gap xs proper > 0
-- gap>0 {b} {d} {o} (x ∙)    proper =
--     start
--         1
--     ≤⟨ m≤m*1+n 1 b ⟩
--         1 * suc b
--     ≤⟨ *n-mono (suc b) (m≤m⊔n 1 o) ⟩
--         carry o * suc b
--     □
-- gap>0 {b} {d} {o} (x ∷ xs) proper =
--     start
--         1
--     ≤⟨ m≤m*1+n 1 b ⟩
--         1 * suc b
--     ≤⟨ *n-mono (suc b) (m≥n+o⇒m∸o≥n ⟦ next-xs ⟧ 1 ⟦ xs ⟧ (next-numeral-is-greater-Proper xs proper)) ⟩
--         (⟦ next-xs ⟧ ∸ ⟦ xs ⟧) * suc b
--     □
--     where
--         next-xs : Numeral (suc b) (suc d) o
--         next-xs = next-numeral-Proper xs proper
--------------------------------------------------------------------------------
-- Properties of next-numeral on Proper Numbers
--------------------------------------------------------------------------------

next-numeral-Proper-refine-target : ∀ {b d o}
    → (xs : Numeral (suc b) (suc d) o)
    → (proper : 2 ≤ suc (d + o))
    → NextView (suc b) (suc d) o xs proper
    → Set
next-numeral-Proper-refine-target xs proper (Interval b d o ¬greatest) = next-numeral-Proper xs proper ≡ next-numeral-Proper-Interval xs ¬greatest proper
next-numeral-Proper-refine-target xs proper (GappedEndpoint b d o greatest gapped) = next-numeral-Proper xs proper ≡ next-numeral-Proper-GappedEndpoint xs proper gapped
next-numeral-Proper-refine-target xs proper (UngappedEndpoint b d o greatest ¬gapped) = next-numeral-Proper xs proper ≡ next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped

next-numeral-Proper-refine : ∀ {b d o}
    → (xs : Numeral (suc b) (suc d) o)
    → (proper : 2 ≤ suc (d + o))
    → (view : NextView (suc b) (suc d) o xs proper)
    → next-numeral-Proper-refine-target xs proper view
next-numeral-Proper-refine xs proper (Interval b d o ¬greatest) with nextView xs proper
next-numeral-Proper-refine xs proper (Interval b d o ¬greatest) | Interval _ _ _ _ = refl
next-numeral-Proper-refine xs proper (Interval b d o ¬greatest) | GappedEndpoint _ _ _ greatest _ = contradiction greatest ¬greatest
next-numeral-Proper-refine xs proper (Interval b d o ¬greatest) | UngappedEndpoint _ _ _ greatest _ = contradiction greatest ¬greatest
next-numeral-Proper-refine xs proper (GappedEndpoint b d o greatest gapped) with nextView xs proper
next-numeral-Proper-refine xs proper (GappedEndpoint b d o greatest gapped) | Interval _ _ _ ¬greatest = contradiction greatest ¬greatest
next-numeral-Proper-refine xs proper (GappedEndpoint b d o greatest gapped) | GappedEndpoint _ _ _ _ _ = refl
next-numeral-Proper-refine xs proper (GappedEndpoint b d o greatest gapped) | UngappedEndpoint _ _ _ _ ¬gapped = contradiction gapped ¬gapped
next-numeral-Proper-refine xs proper (UngappedEndpoint b d o greatest ¬gapped) with nextView xs proper
next-numeral-Proper-refine xs proper (UngappedEndpoint b d o greatest ¬gapped) | Interval _ _ _ ¬greatest = contradiction greatest ¬greatest
next-numeral-Proper-refine xs proper (UngappedEndpoint b d o greatest ¬gapped) | GappedEndpoint _ _ _ _ gapped = contradiction gapped ¬gapped
next-numeral-Proper-refine xs proper (UngappedEndpoint b d o greatest ¬gapped) | UngappedEndpoint _ _ _ _ _ = refl


--------------------------------------------------------------------------------
-- next-numeral-is-immediate-Proper
--------------------------------------------------------------------------------

next-numeral-is-immediate-Proper : ∀ {b d o}
    → (xs : Numeral (suc b) (suc d) o)
    → (ys : Numeral (suc b) (suc d) o)
    → (proper : 2 ≤ suc (d + o))
    → ⟦ ys ⟧ > ⟦ xs ⟧
    → ⟦ ys ⟧ ≥ ⟦ next-numeral-Proper xs proper ⟧
next-numeral-is-immediate-Proper xs ys proper prop with nextView xs proper
next-numeral-is-immediate-Proper xs ys proper prop | Interval b d o ¬greatest =
    start
        ⟦ next-numeral-Proper-Interval xs ¬greatest proper ⟧
    ≈⟨ next-numeral-Proper-Interval-lemma xs ¬greatest proper ⟩
        suc ⟦ xs ⟧
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □
next-numeral-is-immediate-Proper xs (y ∙) proper prop | GappedEndpoint b d o greatest gapped
    = contradiction prop $ >⇒≰ $
        start
            suc (Digit-toℕ y o)
        ≤⟨ s≤s (greatest-of-all o (lsd xs) y greatest) ⟩
            suc (Digit-toℕ (lsd xs) o)
        ≤⟨ s≤s (lsd-toℕ xs) ⟩
            suc ⟦ xs ⟧
        □
next-numeral-is-immediate-Proper (x ∙) (y ∷ ys) proper prop | GappedEndpoint b d o greatest gapped =
    start
        o + (Digit-toℕ (carry-digit d o proper) o) * suc b
    ≈⟨ cong (λ w → o + w * suc b) (carry-digit-toℕ d o proper) ⟩
        o + carry o * suc b
    ≤⟨ n+-mono o (*n-mono (suc b) ys-lower-bound) ⟩
        o + ⟦ ys ⟧ * suc b
    ≤⟨ +n-mono (⟦ ys ⟧ * suc b) (n≤m+n (Fin.toℕ y) o) ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □
    where
        ≥carry : ∀ {b d o}
            → (xs : Numeral (suc b) (suc d) o)
            → (proper : 2 ≤ suc (d + o))
            → ⟦ xs ⟧ > 0
            → ⟦ xs ⟧ ≥ carry o
        ≥carry {_} {_} {zero}  xs proper prop = prop
        ≥carry {_} {_} {suc o} (x ∙) proper prop = n≤m+n (Fin.toℕ x) (suc o)
        ≥carry {b} {_} {suc o} (x ∷ xs) proper prop =
            start
                suc o
            ≤⟨ n≤m+n (Fin.toℕ x) (suc o) ⟩
                Fin.toℕ x + suc o
            ≤⟨ m≤m+n (Fin.toℕ x + suc o) (⟦ xs ⟧ * suc b) ⟩
                Fin.toℕ x + suc o + ⟦ xs ⟧ * suc b
            □

        ys-lower-bound : ⟦ ys ⟧ ≥ carry o
        ys-lower-bound = ≥carry ys proper (tail-mono-strict-Null x y ys greatest prop)

next-numeral-is-immediate-Proper (x ∷ xs) (y ∷ ys) proper prop | GappedEndpoint b d o greatest gapped =
    start
        o + ⟦ next-xs ⟧ * suc b
    ≤⟨ n+-mono o (*n-mono (suc b) ⟦next-xs⟧≤⟦ys⟧) ⟩
        o + ⟦ ys ⟧ * suc b
    ≤⟨ +n-mono (⟦ ys ⟧ * suc b) (n≤m+n (Fin.toℕ y) o) ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □
    where
        next-xs : Numeral (suc b) (suc d) o
        next-xs = next-numeral-Proper xs proper

        ⟦xs⟧<⟦ys⟧ : ⟦ xs ⟧ < ⟦ ys ⟧
        ⟦xs⟧<⟦ys⟧ = tail-mono-strict x xs y ys greatest prop

        ⟦next-xs⟧≤⟦ys⟧ : ⟦ next-xs ⟧ ≤ ⟦ ys ⟧
        ⟦next-xs⟧≤⟦ys⟧ = next-numeral-is-immediate-Proper xs ys proper ⟦xs⟧<⟦ys⟧

next-numeral-is-immediate-Proper xs ys proper prop | UngappedEndpoint b d o greatest ¬gapped =
    start
        ⟦ next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped ⟧
    ≈⟨ next-numeral-Proper-UngappedEndpoint-lemma xs greatest proper ¬gapped ⟩
        suc ⟦ xs ⟧
    ≤⟨ prop ⟩
        ⟦ ys ⟧
    □

--------------------------------------------------------------------------------
-- next-numeral
--------------------------------------------------------------------------------

next-numeral : ∀ {b d o}
    → (xs : Numeral b d o)
    → ¬ (Maximum xs)
    → Numeral b d o
next-numeral {b} {d} {o} xs ¬max with numView b d o
next-numeral xs ¬max | NullBase d o = next-numeral-NullBase xs ¬max
next-numeral xs ¬max | NoDigits b o = NoDigits-explode xs
next-numeral xs ¬max | AllZeros b   = contradiction (Maximum-AllZeros xs) ¬max
next-numeral xs ¬max | Proper b d o proper = next-numeral-Proper xs proper


--------------------------------------------------------------------------------
-- next-numeral-is-greater
--------------------------------------------------------------------------------


next-numeral-is-greater : ∀ {b d o}
    → (xs : Numeral b d o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ next-numeral xs ¬max ⟧ > ⟦ xs ⟧
next-numeral-is-greater {b} {d} {o} xs ¬max with numView b d o
next-numeral-is-greater xs ¬max | NullBase d o = next-numeral-is-greater-NullBase xs ¬max
next-numeral-is-greater xs ¬max | NoDigits b o = NoDigits-explode xs
next-numeral-is-greater xs ¬max | AllZeros b   = contradiction (Maximum-AllZeros xs) ¬max
next-numeral-is-greater xs ¬max | Proper b d o proper = next-numeral-is-greater-Proper xs proper

--------------------------------------------------------------------------------
-- next-numeral-is-immediate
--------------------------------------------------------------------------------

next-numeral-is-immediate : ∀ {b d o}
    → (xs : Numeral b d o)
    → (ys : Numeral b d o)
    → (¬max : ¬ (Maximum xs))
    → ⟦ ys ⟧ > ⟦ xs ⟧
    → ⟦ ys ⟧ ≥ ⟦ next-numeral xs ¬max ⟧
next-numeral-is-immediate {b} {d} {o} xs ys ¬max prop with numView b d o
next-numeral-is-immediate xs ys ¬max prop | NullBase d o = next-numeral-is-immediate-NullBase xs ys ¬max prop
next-numeral-is-immediate xs ys ¬max prop | NoDigits b o = NoDigits-explode xs
next-numeral-is-immediate xs ys ¬max prop | AllZeros b = contradiction (Maximum-AllZeros xs) ¬max
next-numeral-is-immediate xs ys ¬max prop | Proper b d o proper = next-numeral-is-immediate-Proper xs ys proper prop

--------------------------------------------------------------------------------
-- properties of the gaps
--------------------------------------------------------------------------------


Gapped#N⇒Gapped#0 : ∀ {b d o}
    → (xs : Numeral (suc b) (suc d) o)
    → (proper : 2 ≤ suc (d + o))
    → Gapped#N b d o xs proper
    → Gapped#0 b d o
Gapped#N⇒Gapped#0 xs proper gapped#N with nextView xs proper
Gapped#N⇒Gapped#0 xs proper gapped#N | Interval b d o ¬greatest =
    start
        suc (suc d)
    ≤⟨ gapped#N ⟩
        (⟦ next-numeral-Proper-Interval xs ¬greatest proper ⟧ ∸ ⟦ xs ⟧) * suc b
    ≤⟨ *n-mono (suc b) $
        start
            ⟦ next-numeral-Proper-Interval xs ¬greatest proper ⟧ ∸ ⟦ xs ⟧
        ≈⟨ cong (λ w → w ∸ ⟦ xs ⟧) (next-numeral-Proper-Interval-lemma xs ¬greatest proper) ⟩
            suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
        ≈⟨ m+n∸n≡m (suc zero) ⟦ xs ⟧ ⟩
            suc zero
        ≤⟨ m≤m⊔n 1 o ⟩
            suc zero ⊔ o
        □
     ⟩
        (suc zero ⊔ o) * suc b
    □
Gapped#N⇒Gapped#0 (x ∙)    proper gapped#N | GappedEndpoint b d o greatest gapped#0 = gapped#0
Gapped#N⇒Gapped#0 (x ∷ xs) proper _        | GappedEndpoint b d o greatest gapped#N = Gapped#N⇒Gapped#0 xs proper gapped#N
Gapped#N⇒Gapped#0 xs proper gapped#N | UngappedEndpoint b d o greatest ¬gapped =
        start
            suc (suc d)
        ≤⟨ gapped#N ⟩
            (⟦ next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped ⟧ ∸ ⟦ xs ⟧) * suc b
        ≤⟨ *n-mono (suc b) $
            start
                ⟦ next-numeral-Proper-UngappedEndpoint xs greatest proper ¬gapped ⟧ ∸ ⟦ xs ⟧
            ≈⟨ cong (λ w → w ∸ ⟦ xs ⟧) (next-numeral-Proper-UngappedEndpoint-lemma xs greatest proper ¬gapped) ⟩
                suc ⟦ xs ⟧ ∸ ⟦ xs ⟧
            ≈⟨ m+n∸n≡m (suc zero) ⟦ xs ⟧ ⟩
                suc zero
            ≤⟨ m≤m⊔n 1 o ⟩
                suc zero ⊔ o
            □
         ⟩
            (suc zero ⊔ o) * suc b
        □

-- ¬Gapped#0⇒¬Gapped#N : ∀ {b d o}
--     → (xs : Numeral (suc b) (suc d) o)
--     → (proper : 2 ≤ suc (d + o))
--     → ¬ (Gapped#0 b d o)
--     → ¬ (Gapped#N b d o xs proper)
-- ¬Gapped#0⇒¬Gapped#N xs proper ¬Gapped#0 = contraposition (Gapped#N⇒Gapped#0 xs proper) ¬Gapped#0

¬Gapped#0⇒¬Gapped : ∀ {b d o}
    → (xs : Numeral (suc b) (suc d) o)
    → (proper : 2 ≤ suc (d + o))
    → ¬ (Gapped#0 b d o)
    → ¬ (Gapped xs proper)
¬Gapped#0⇒¬Gapped (x ∙)    proper ¬Gapped#0 = ¬Gapped#0
¬Gapped#0⇒¬Gapped (x ∷ xs) proper ¬Gapped#0 = contraposition
    (Gapped#N⇒Gapped#0 xs proper)
    ¬Gapped#0
