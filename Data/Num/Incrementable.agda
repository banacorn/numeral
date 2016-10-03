module Data.Num.Incrementable where

open import Data.Num.Core
open import Data.Num.Maximum

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

Incrementable : ∀ {b d o} → Num b d o → Set
Incrementable {b} {d} {o} xs = Σ[ xs' ∈ Num b d o ] toℕ xs' ≡ suc (toℕ xs)

------------------------------------------------------------------------
-- Views

-- when a system has no digits at all
Incrementable-lemma-1 : ∀ {b o} → (xs : Num b 0 o) → ¬ (Incrementable xs)
Incrementable-lemma-1 ∙ (∙ , ())
Incrementable-lemma-1 ∙ (() ∷ xs , p)
Incrementable-lemma-1 (() ∷ xs)

Num-b-1-0⇒≡0 : ∀ {b} → (xs : Num b 1 0) → toℕ xs ≡ 0
Num-b-1-0⇒≡0     ∙           = refl
Num-b-1-0⇒≡0 {b} (z    ∷ xs) = cong (λ w → w * b) (Num-b-1-0⇒≡0 xs)
Num-b-1-0⇒≡0     (s () ∷ xs)

-- when a system has only the digit 0
Incrementable-lemma-2 : ∀ {b} → (xs : Num b 1 0) → ¬ (Incrementable xs)
Incrementable-lemma-2 {b} xs (xs' , p) = contradiction (
    begin
        0
    ≡⟨ sym (Num-b-1-0⇒≡0 xs') ⟩
        toℕ xs'
    ≡⟨ p ⟩
        suc (toℕ xs)
    ≡⟨ cong suc (Num-b-1-0⇒≡0 xs) ⟩
        1
    ∎) (λ ())


Incrementable-lemma-3 : ∀ {b d o} → ¬ (Incrementable {b} {suc d} {suc (suc o)} ∙)
Incrementable-lemma-3 (∙ , ())
Incrementable-lemma-3 (x ∷ xs , ())

Incrementable-lemma-4 : ∀ {d o}
    → (x : Digit (suc d)) → (xs : Num 0 (suc d) o)
    → suc (Fin.toℕ x) ≡ suc d
    → ¬ (Incrementable (x ∷ xs))
Incrementable-lemma-4 x xs p (∙ , ())
Incrementable-lemma-4 {d} {o} x xs p (x' ∷ xs' , q) =
    let x'≡1+x : Fin.toℕ x' ≡ suc (Fin.toℕ x)
        x'≡1+x  = cancel-+-right o
                $ cancel-+-right 0
                $ begin
                        Fin.toℕ x' + o + zero
                    ≡⟨ cong (_+_ (Digit-toℕ x' o)) (sym (*-right-zero (toℕ xs'))) ⟩
                        Fin.toℕ x' + o + toℕ xs' * zero
                    ≡⟨ q ⟩
                        suc (Fin.toℕ x + o + toℕ xs * zero)
                    ≡⟨ cong (_+_ (suc (Digit-toℕ x o))) (*-right-zero (toℕ xs)) ⟩
                        suc (Fin.toℕ x + o + zero)
                    ∎
        x'≡1+d : Fin.toℕ x' ≡ suc d
        x'≡1+d =
            begin
                Fin.toℕ x'
            ≡⟨ x'≡1+x ⟩
                suc (Fin.toℕ x)
            ≡⟨ p ⟩
                suc d
            ∎
        x'≢1+d : Fin.toℕ x' ≢ suc d
        x'≢1+d = <⇒≢ (bounded x')
    in contradiction x'≡1+d x'≢1+d

-- Incrementable-lemma-5 : ∀ {b d o}
--     → (x : Digit (suc d))
--     → (xs xs' : Num (suc b) (suc d) o)
--     → toℕ xs' ≡ suc (toℕ xs)
--     → (redundant : suc b ≤ suc d)
--     → (greatest : Greatest x)
--     → toℕ (digit+1-b x {!   !} {!   !} redundant greatest ∷ xs') ≡ suc (toℕ (x ∷ xs))
-- Incrementable-lemma-5 {b} {d} {o} x xs xs' p redundant greatest = {!   !}
    -- begin
    --     toℕ (digit+1-b x ? ? redundant greatest ∷ xs')
    -- ≡⟨ refl ⟩
    --     Digit-toℕ (digit+1-b x ? ? redundant greatest) o + toℕ xs' * suc b
    -- -- fuse Digit-toℕ with digit+1-b
    -- ≡⟨ cong (λ w → w + toℕ xs' * suc b) (Digit-toℕ-digit+1-b x ? ? redundant greatest) ⟩
    --     Fin.toℕ x ∸ b + o + toℕ xs' * suc b
    -- -- p : toℕ xs' ≡ suc (toℕ xs)
    -- ≡⟨ cong (λ w → (Fin.toℕ x ∸ b) + o + w * suc b) p ⟩
    -- -- moving things around
    --     Fin.toℕ x ∸ b + o + suc (b + toℕ xs * suc b)
    -- ≡⟨ +-suc (Fin.toℕ x ∸ b + o) (b + toℕ xs * suc b) ⟩
    --     suc (Fin.toℕ x ∸ b + o + (b + toℕ xs * suc b))
    -- ≡⟨ sym (+-assoc (suc (Fin.toℕ x ∸ b + o)) b (toℕ xs * suc b)) ⟩
    --     suc (Fin.toℕ x ∸ b + o + b + toℕ xs * suc b)
    -- ≡⟨ cong (λ w → suc (w + toℕ xs * suc b)) ([a+b]+c≡[a+c]+b (Fin.toℕ x ∸ b) o b) ⟩
    --     suc (Fin.toℕ x ∸ b + b + o + toℕ xs * suc b)
    -- -- remove that annoying "∸ b + b"
    -- ≡⟨ cong (λ w → suc (w + o + toℕ xs * suc b)) (m∸n+n $ ≤-pred $
    --     start
    --         suc b
    --     ≤⟨ redundant ⟩
    --         suc d
    --     ≤⟨ reflexive (sym greatest) ⟩
    --         suc (Fin.toℕ x)
    --     □ ) ⟩
    --     suc (Fin.toℕ x + o + toℕ xs * suc b)
    -- ∎


-- Incrementable-lemma-6 : ∀ {b d o}
--     → (x : Digit (suc d))
--     → (xs : Num (suc b) (suc d) o)
--     → (b>d : suc b > suc d)
--     → Greatest x
--     → Incrementable (x ∷ xs)
--     → ⊥
-- Incrementable-lemma-6 x xs b>d greatest (∙ , ())
-- Incrementable-lemma-6 {b} {d} {o} x xs b>d greatest (y ∷ ys , claim)
--     = contradiction claim (>⇒≢ ⟦y∷ys⟧>1+⟦x∷xs⟧)
--     where
--         ⟦x∷xs⟧<⟦y∷ys⟧ : toℕ (x ∷ xs) < toℕ (y ∷ ys)
--         ⟦x∷xs⟧<⟦y∷ys⟧ = m≡n+o⇒m≥o {toℕ (y ∷ ys)} {suc (toℕ (x ∷ xs) )} zero claim
--         ⟦xs⟧<⟦ys⟧ : toℕ xs < toℕ ys
--         ⟦xs⟧<⟦ys⟧ = tail-mono-strict x y xs ys greatest ⟦x∷xs⟧<⟦y∷ys⟧
--         ⟦y∷ys⟧>1+⟦x∷xs⟧ : toℕ (y ∷ ys) > suc (toℕ (x ∷ xs))
--         ⟦y∷ys⟧>1+⟦x∷xs⟧ =
--             start
--                 suc (suc (toℕ (x ∷ xs)))
--             ≤⟨ ≤-refl ⟩
--                 suc (suc (Digit-toℕ x o + toℕ xs * suc b))
--             ≤⟨ reflexive (sym (+-suc (suc (Digit-toℕ x o)) (toℕ xs * suc b))) ⟩
--                 suc (Digit-toℕ x o) + suc (toℕ xs * suc b)
--             ≤⟨ +n-mono (suc (toℕ xs * suc b)) (Digit<d+o x o) ⟩
--                 suc (d + o + suc (toℕ xs * suc b))
--             ≤⟨ reflexive $
--                 begin
--                     (suc d + o) + suc (toℕ xs * suc b)
--                 ≡⟨ +-suc (suc d + o) (toℕ xs * suc b) ⟩
--                     2 + (d + o + toℕ xs * suc b)
--                 ≡⟨ cong (_+_ 2) (+-assoc d o (toℕ xs * suc b)) ⟩
--                     2 + (d + (o + toℕ xs * suc b))
--                 ≡⟨ sym (+-assoc 2 d (o + toℕ xs * suc b)) ⟩
--                     (2 + d) + (o + toℕ xs * suc b)
--                 ≡⟨ a+[b+c]≡b+[a+c] ((2 + d)) o (toℕ xs * suc b) ⟩
--                     o + ((2 + d) + toℕ xs * suc b)
--                 ∎ ⟩
--                 o + suc (suc (d + toℕ xs * suc b))
--             ≤⟨ +n-mono ((suc (suc d) + toℕ xs * suc b)) (+n-mono o {zero} {Fin.toℕ y} z≤n) ⟩
--                 Digit-toℕ y o + (suc (suc d) + toℕ xs * suc b)
--             ≤⟨ n+-mono (Digit-toℕ y o) (+n-mono (toℕ xs * suc b) b>d) ⟩
--                 Digit-toℕ y o + (suc b + toℕ xs * suc b)
--             ≤⟨ ≤-refl ⟩
--                 Digit-toℕ y o + suc (toℕ xs) * suc b
--             ≤⟨ n+-mono (Digit-toℕ y o) (*n-mono (suc b) ⟦xs⟧<⟦ys⟧) ⟩
--                 Digit-toℕ y o + toℕ ys * suc b
--             ≤⟨ ≤-refl ⟩
--                 toℕ (y ∷ ys)
--             □

-- Incrementable-lemma-7 : ∀ {b d o}
--     → (x : Digit (suc d))
--     → (xs : Num (suc b) (suc d) o)
--     → Greatest x
--     → ¬ (Incrementable xs)
--     → Incrementable (x ∷ xs)
--     → ⊥
-- Incrementable-lemma-7 x xs greatest ¬p (∙ , ())
-- Incrementable-lemma-7 x xs greatest ¬p (y ∷ ys , claim) = {! ⟦xs⟧<⟦ys⟧  !}
    -- ¬p : Σ[ xs' ∈ _ ] toℕ xs' ≡ suc (toℕ xs) → ⊥
    -- p0 : toℕ (y ∷ ys) > toℕ (x ∷ xs)
    -- toℕ ys > toℕ xs
    -- where
    --     ⟦x∷xs⟧<⟦y∷ys⟧ : toℕ (x ∷ xs) < toℕ (y ∷ ys)
    --     ⟦x∷xs⟧<⟦y∷ys⟧ = m≡n+o⇒m≥o {toℕ (y ∷ ys)} {suc (toℕ (x ∷ xs) )} zero claim
    --     ⟦xs⟧<⟦ys⟧ : toℕ xs < toℕ ys
    --     ⟦xs⟧<⟦ys⟧ = tail-mono-strict x y xs ys greatest ⟦x∷xs⟧<⟦y∷ys⟧

Incrementable-lemma-8 : ∀ {b d o}
    → (xs : Num b (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → toℕ (next-number xs ¬max) ∸ toℕ xs > 0
Incrementable-lemma-8 xs ¬max =
    start
        suc zero
    ≤⟨ reflexive (sym (m+n∸n≡m 1 (toℕ xs))) ⟩
        suc (toℕ xs) ∸ toℕ xs
    ≤⟨ ∸-mono {suc (toℕ xs)} {toℕ (next-number xs ¬max)} {toℕ xs} {toℕ xs} (next-number-is-greater xs ¬max) ≤-refl ⟩
        toℕ (next-number xs ¬max) ∸ toℕ xs
    □

Incrementable-lemma-9 : ∀ {b d o}
    → (xs : Num (suc b) (suc d) o)
    → (¬max : ¬ (Maximum xs))
    → (toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b > 0
Incrementable-lemma-9 xs ¬max = (Incrementable-lemma-8 xs ¬max) *-mono (s≤s z≤n)

Incrementable-lemma-10 : ∀ {b d o}
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → (greatest : Greatest x)
    → (¬max : ¬ (Maximum xs))
    → let base = (toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b in
      (redundant : Redundant base (suc d))
    → toℕ (digit+1-b x base (Incrementable-lemma-9 xs ¬max) redundant greatest ∷ next-number xs ¬max) ≡ suc (toℕ (x ∷ xs))
Incrementable-lemma-10 {b} {d} {o} x xs greatest ¬max redundant =
    let
        A = toℕ (next-number xs ¬max) * suc b
        B = toℕ xs * suc b
        P =
            start
                toℕ (next-number xs ¬max) * suc b ∸ toℕ xs * suc b
            ≤⟨ reflexive (sym (*-distrib-∸ʳ (suc b) (toℕ (next-number xs ¬max)) (toℕ xs))) ⟩
                (toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b
            ≤⟨ ≤-pred redundant ⟩
                d
            ≤⟨ m≤m+n d (suc o) ⟩
                d + suc o
            ≤⟨ reflexive (+-suc d o) ⟩
                suc (d + o)
            ≤⟨ s≤s $ reflexive (sym (toℕ-greatest x greatest)) ⟩
                suc (Fin.toℕ x + o)
            □
    in
    begin
        toℕ (digit+1-b x ((toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b) (Incrementable-lemma-9 xs ¬max) redundant greatest ∷ next-number xs ¬max)
    ≡⟨ refl ⟩
        Digit-toℕ (digit+1-b x ((toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b) (Incrementable-lemma-9 xs ¬max) redundant greatest) o + A
    ≡⟨ cong (λ w → w + A) (Digit-toℕ-digit+1-b x ((toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b) (Incrementable-lemma-9 xs ¬max) redundant greatest) ⟩
        suc (Digit-toℕ x o) ∸ (toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b + A
    ≡⟨ cong (λ w → suc (Digit-toℕ x o) ∸ w + A) (*-distrib-∸ʳ (suc b) (toℕ (next-number xs ¬max)) (toℕ xs)) ⟩
        suc (Digit-toℕ x o) ∸ (A ∸ B) + A
    ≡⟨ +-comm (suc (Digit-toℕ x o) ∸ (A ∸ B)) A ⟩
        A + (suc (Digit-toℕ x o) ∸ (A ∸ B))
    ≡⟨ cong (λ w → w + (suc (Digit-toℕ x o) ∸ (A ∸ B))) (sym (m+n∸m≡n {B} {A} (*n-mono (suc b) (≤-pred (≤-step (next-number-is-greater xs ¬max)))))) ⟩
        B + (A ∸ B) + (suc (Digit-toℕ x o) ∸ (A ∸ B))
    ≡⟨ +-assoc B (A ∸ B) (suc (Digit-toℕ x o) ∸ (A ∸ B)) ⟩
        B + ((A ∸ B) + (suc (Digit-toℕ x o) ∸ (A ∸ B)))
    ≡⟨ cong (λ w → B + w) (m+n∸m≡n {A ∸ B} P) ⟩
        B + suc (Digit-toℕ x o)
    ≡⟨ +-comm (toℕ xs * suc b) (suc (Fin.toℕ x + o)) ⟩
        suc (Fin.toℕ x + o + toℕ xs * suc b)
    ≡⟨ refl ⟩
        suc (toℕ (x ∷ xs))
    ∎

Maximum⇒¬Incrementable : ∀ {b d o}
    → (xs : Num b d o)
    → Maximum xs
    → ¬ (Incrementable xs)
Maximum⇒¬Incrementable xs max (evidence , claim)
    = contradiction claim (<⇒≢ (s≤s (max evidence)))


tail-mono-strict : ∀ {b d o} (x y : Digit d) (xs ys : Num b d o)
    → Greatest x
    → toℕ (x ∷ xs) < toℕ (y ∷ ys)
    → toℕ xs < toℕ ys
tail-mono-strict {b} {_} {o} x y xs ys greatest p
    = *n-mono-strict-inverse b ⟦∷xs⟧<⟦∷ys⟧
    where
        ⟦x⟧≥⟦y⟧ : Digit-toℕ x o ≥ Digit-toℕ y o
        ⟦x⟧≥⟦y⟧ = greatest-of-all o x y greatest
        ⟦∷xs⟧<⟦∷ys⟧ : toℕ xs * b < toℕ ys * b
        ⟦∷xs⟧<⟦∷ys⟧ = +-mono-contra ⟦x⟧≥⟦y⟧ p
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
Incrementable-lemma-11 : ∀ {b d o}
    → (x : Digit (suc d))
    → (xs : Num (suc b) (suc d) o)
    → (greatest : Greatest x)
    → (¬max : ¬ (Maximum xs))
    → (¬redundant : ¬ (Redundant ((toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b) (suc d)))
    → ¬ (Incrementable (x ∷ xs))
Incrementable-lemma-11 {b} {d} {o} x xs greatest ¬max ¬redundant (∙ , ())
Incrementable-lemma-11 {b} {d} {o} x xs greatest ¬max ¬redundant (y ∷ ys , claim) = {!   !}
    where   ⟦ys⟧>⟦xs⟧ : toℕ ys > toℕ xs
            ⟦ys⟧>⟦xs⟧ = tail-mono-strict x y xs ys greatest (m≡n+o⇒m≥o 0 claim)

            ⟦y∷ys⟧>1+⟦x∷xs'⟧ : toℕ (y ∷ ys) > suc (toℕ (x ∷ xs))
            ⟦y∷ys⟧>1+⟦x∷xs⟧ =
                start
                    suc (suc (Fin.toℕ x + o + toℕ xs * suc b))
                ≤⟨ {!   !} ⟩
                    {!   !}
                ≤⟨ {!   !} ⟩
                    {!   !}
                ≤⟨ {!   !} ⟩
                    {!   !}
                ≤⟨ {!   !} ⟩
                    {!   !}
                ≤⟨ {!   !} ⟩
                    {!   !}
                ≤⟨ {!   !} ⟩
                    {!   !}
                ≤⟨ {!   !} ⟩
                    Fin.toℕ y + o + toℕ ys * suc b
                □
            -- ⟦y∷ys⟧>1+⟦x∷xs⟧ : toℕ (y ∷ ys) > suc (toℕ (x ∷ xs))
            -- ⟦y∷ys⟧>1+⟦x∷xs⟧ =
            --     start
            --         suc (suc (Fin.toℕ x + o + toℕ xs * suc b))
            --     ≤⟨ {!   !} ⟩
            --         {!   !}
            --     ≤⟨ {!   !} ⟩
            --         {!   !}
            --     ≤⟨ {!   !} ⟩
            --         {!   !}
            --     ≤⟨ {!   !} ⟩
            --         {!   !}
            --     ≤⟨ {!   !} ⟩
            --         {!   !}
            --     ≤⟨ {!   !} ⟩
            --         {!   !}
            --     ≤⟨ {!   !} ⟩
            --         Fin.toℕ y + o + toℕ ys * suc b
            --     □

            -- with toℕ ys ≟ toℕ (next-number xs ¬max)
-- Incrementable-lemma-11 x xs greatest ¬max ¬redundant (y ∷ ys , claim) | yes p = {!   !}
-- Incrementable-lemma-11 x xs greatest ¬max ¬redundant (y ∷ ys , claim) | no ¬p = {!   !}
    -- where   ⟦evidence⟧>1+⟦x∷xs⟧ : toℕ evidence > suc (Digit-toℕ x o + toℕ xs * suc b)
    --         ⟦evidence⟧>1+⟦x∷xs⟧ =
    --             start
    --                 suc (suc (Fin.toℕ x + o + toℕ xs * suc b))
    --             ≤⟨ reflexive (cong (λ w → suc (w + o + toℕ xs * suc b)) greatest) ⟩
    --                 suc (suc (d + o) + toℕ xs * suc b)
    --             ≤⟨ reflexive (+-assoc (suc (suc d)) o (toℕ xs * suc b)) ⟩
    --                 suc (suc (d + (o + toℕ xs * suc b)))
    --             ≤⟨ +n-mono (o + toℕ xs * suc b) (≰⇒> ¬redundant) ⟩
    --                 suc ((toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b) + (o + toℕ xs * suc b)
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 suc (Fin.toℕ x + o + toℕ xs * suc b)
    --             ≤⟨ reflexive (sym claim) ⟩
    --                 toℕ evidence
    --             □
    -- where   redundant : Redundant ((toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b) (suc d)
    --         redundant = +n-mono-inverse (toℕ xs * suc b) $
    --             start
    --                 suc ((toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b) + toℕ xs * suc b
    --             ≤⟨ reflexive (cong (λ w → suc w + toℕ xs * suc b) (*-distrib-∸ʳ (suc b) (toℕ (next-number xs ¬max)) (toℕ xs))) ⟩
    --                 suc (toℕ (next-number xs ¬max) * suc b ∸ toℕ xs * suc b) + toℕ xs * suc b
    --             ≤⟨ s≤s (reflexive (m∸n+n {_} {toℕ xs * suc b} (*n-mono (suc b) (≤-pred $ ≤-step (next-number-is-greater xs ¬max))))) ⟩
    --                 suc (toℕ (next-number xs ¬max) * suc b)
    --             ≤⟨ {! ≰⇒> ¬redundant  !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!   !}
    --             ≤⟨ {!   !} ⟩
    --                 {!    !}
    --             ≤⟨ ≤-refl ⟩
    --                 suc (Fin.toℕ x) + toℕ xs * suc b
    --             ≤⟨ {!   !} ⟩
    --                 suc d + toℕ xs * suc b
    --             □



Incrementable? : ∀ {b d o} → (xs : Num b d o) → Dec (Incrementable xs)
-- having no digit at all
-- Incrementable? xs  = {!   !}
Incrementable? {_} {zero}                     xs = no (Incrementable-lemma-1 xs)
Incrementable? {_} {suc zero}    {zero}        ∙ = no (Incrementable-lemma-2 ∙)
Incrementable? {_} {suc (suc d)} {zero}        ∙ = yes (fromℕ≤ {1} (s≤s (s≤s z≤n)) ∷ ∙ , refl)
Incrementable? {_} {suc d}       {suc zero}    ∙ = yes ((z ∷ ∙) , refl)
Incrementable? {_} {suc d}       {suc (suc o)} ∙ = no Incrementable-lemma-3
Incrementable? {_} {suc d}       (x ∷ xs) with Greatest? x
Incrementable? {zero} {suc d} (x ∷ xs) | yes greatest = no {!   !}
Incrementable? {suc b} {suc d}       (x ∷ xs) | yes greatest with Maximum? xs
Incrementable? {suc b} {suc d}       (x ∷ xs) | yes greatest | yes max = no {!   !}
Incrementable? {suc b} {suc d}       (x ∷ xs) | yes greatest | no ¬max with Redundant? ((toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b) (suc d)
Incrementable? {suc b} {suc d} {o}   (x ∷ xs) | yes greatest | no ¬max | yes redundant
    = yes (digit+1-b {suc d} x ((toℕ (next-number xs ¬max) ∸ toℕ xs) * suc b) (Incrementable-lemma-9 xs ¬max) redundant greatest ∷ next-number xs ¬max , Incrementable-lemma-10 x xs greatest ¬max redundant)
Incrementable? {suc b} {suc d}       (x ∷ xs) | yes greatest | no ¬max | no ¬redundant
    = no (Incrementable-lemma-11 x xs greatest ¬max ¬redundant)
Incrementable? {b} {suc d}       (x ∷ xs) | no ¬greatest = yes {!   !}


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




-- Incrementable? {zero} {suc d} (x ∷ xs) | yes greatest = no (Incrementable-lemma-4 x xs greatest)
-- Incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest with Incrementable? xs
-- Incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | yes incr with suc (suc b) ≤? suc d
-- Incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | yes (xs' , incr) | yes redundant
--     = yes ((digit+1-b x (suc b) (s≤s z≤n) redundant greatest  ∷ xs') , {!   !})
--     -- = yes (digit+1-b x {! suc b  !} {!   !} {!   !} greatest ∷ xs' , Incrementable-lemma-5 x xs xs' incr ? greatest)
-- Incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | yes incr | no ¬r
--     = no {!   !}
--     -- = no (Incrementable-lemma-6 x xs (≰⇒> ¬r) greatest)
-- Incrementable? {suc b} {suc d} {o} (x ∷ xs) | yes greatest | no ¬incr with suc (suc b * o) ≤? suc d
-- Incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | no ¬incr | yes p with Maximum? xs
-- Incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | no ¬incr | yes p | yes max
--     = no {!   !}
-- Incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | no ¬incr | yes p | no ¬max
--     = yes {!   !}
--     -- = yes ({!   !} ∷ next xs {!   !} , {!   !})
-- Incrementable? {suc b} {suc d} (x ∷ xs) | yes greatest | no ¬incr | no ¬p
--     = no {!   !}
-- Incrementable? {b} {suc d} (x ∷ xs) | no ¬greatest
--     = yes {!   !}


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
