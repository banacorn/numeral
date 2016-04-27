module Data.Num.Properties where

open import Data.Num

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin.Properties hiding (setoid)
open import Data.Nat.DM
open import Data.Fin as Fin
    using (Fin; #_; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)

open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)


-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- □


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

toℕ-⊹-homo : ∀ {b d o}
    → {isSurj : IsSurjective b d o}
    → (xs ys : Num b d o)
    → toℕ (_⊹_ {isSurj = isSurj} xs ys) ≡ toℕ xs + toℕ ys
toℕ-⊹-homo {b} {d} {o} xs       ys        with surjectionView b d o
toℕ-⊹-homo             ∙        ∙        | Surj condition = refl
toℕ-⊹-homo             ∙        (y ∷ ys) | Surj condition = refl
toℕ-⊹-homo             (x ∷ xs) ∙        | Surj condition = sym (+-right-identity (toℕ (x ∷ xs)))
toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | Surj condition with _divMod_ (o + Fin.toℕ x + Fin.toℕ y) b {fromWitnessFalse (>⇒≢ (SurjCond⇒b≥1 condition))}
toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | Surj condition | result quotient remainder property div-eq mod-eq =
    let sum = (_⊹_ {isSurj = SurjCond⇒IsSurj condition} xs ys) in
    begin
        toℕ (inject≤ remainder d≥b ∷ n+ quotient sum)
    ≡⟨ refl ⟩
        o + Fin.toℕ (inject≤ remainder d≥b) + toℕ (n+ quotient sum) * b
    ≡⟨ cong (λ w → o + w + toℕ (n+ quotient sum) * b) (inject≤-lemma remainder d≥b) ⟩
        o + Fin.toℕ remainder + toℕ (n+ quotient sum) * b
    ≡⟨ cong (λ w → o + Fin.toℕ remainder + w * b) (toℕ-n+ {isSurj = isSurjective} quotient (sum)) ⟩
        o + Fin.toℕ remainder + (quotient + (toℕ sum)) * b
    ≡⟨ cong (λ w → o + Fin.toℕ remainder + w) (distribʳ-*-+ b quotient (toℕ sum)) ⟩
        o + Fin.toℕ remainder + (quotient * b + toℕ sum * b)
    ≡⟨ +-assoc o (Fin.toℕ remainder) (quotient * b + toℕ sum * b) ⟩
        o + (Fin.toℕ remainder + (quotient * b + toℕ sum * b))
    ≡⟨ cong (λ w → o + w) (sym (+-assoc (Fin.toℕ remainder) (quotient * b) (toℕ sum * b))) ⟩
        o + (Fin.toℕ remainder + quotient * b + toℕ sum * b)
    ≡⟨ cong (λ w → o + (w + toℕ sum * b)) (sym property) ⟩
        o + (o + Fin.toℕ x + Fin.toℕ y + toℕ sum * b)
    ≡⟨ cong (λ w → o + (o + Fin.toℕ x + Fin.toℕ y + w * b)) (toℕ-⊹-homo {isSurj = isSurjective} xs ys) ⟩
        o + (o + Fin.toℕ x + Fin.toℕ y + (toℕ xs + toℕ ys) * b)
    ≡⟨ cong (λ w → o + (o + Fin.toℕ x + Fin.toℕ y + w)) (distribʳ-*-+ b (toℕ xs) (toℕ ys)) ⟩
        o + ((o + Fin.toℕ x) + Fin.toℕ y + (toℕ xs * b + toℕ ys * b))
    ≡⟨ cong (λ w → o + w) (+-assoc (o + Fin.toℕ x) (Fin.toℕ y) (toℕ xs * b + toℕ ys * b)) ⟩
        o + (o + Fin.toℕ x + (Fin.toℕ y + (toℕ xs * b + toℕ ys * b)))
    ≡⟨ cong (λ w → o + (o + Fin.toℕ x + w)) (a+[b+c]≡b+[a+c] (Fin.toℕ y) (toℕ xs * b) (toℕ ys * b)) ⟩
        o + (o + Fin.toℕ x + (toℕ xs * b + (Fin.toℕ y + toℕ ys * b)))
    ≡⟨ cong (λ w → o + w) (sym (+-assoc (o + Fin.toℕ x) (toℕ xs * b) (Fin.toℕ y + toℕ ys * b))) ⟩
        o + ((o + Fin.toℕ x + toℕ xs * b) + (Fin.toℕ y + toℕ ys * b))
    ≡⟨ a+[b+c]≡b+[a+c] o (o + Fin.toℕ x + toℕ xs * b) (Fin.toℕ y + toℕ ys * b) ⟩
        (o + Fin.toℕ x + toℕ xs * b) + (o + (Fin.toℕ y + toℕ ys * b))
    ≡⟨ cong (λ w → o + Fin.toℕ x + toℕ xs * b + w) (sym (+-assoc o (Fin.toℕ y) (toℕ ys * b))) ⟩
        (o + Fin.toℕ x + toℕ xs * b) + (o + Fin.toℕ y + toℕ ys * b)
    ∎
    where   d≥b : d ≥ b
            d≥b = SurjCond⇒d≥b condition
            isSurjective = SurjCond⇒IsSurj condition
toℕ-⊹-homo {isSurj = ()}  xs ys | NonSurj _


-- toℕ-⊹-homo : ∀ {b d o}
--     → {surj : True (Surjective? b d o)}
--     → (xs ys : Num b d o)
--     → toℕ (_⊹_ {surj = surj} xs ys) ≡ toℕ xs + toℕ ys
-- toℕ-⊹-homo {b} {d} {o} xs       ys        with surjectionView b d o
-- toℕ-⊹-homo {b} {d} {o} xs       ys        | Surj cond with Surjective? b d o
-- toℕ-⊹-homo {b} {d} {o} ∙        ∙        | Surj cond | yes surj = refl
-- toℕ-⊹-homo {b} {d} {o} ∙        (y ∷ ys) | Surj cond | yes surj = refl
-- toℕ-⊹-homo {b} {d} {o} (x ∷ xs) ∙        | Surj cond | yes surj = sym (+-right-identity (toℕ (x ∷ xs)))
-- toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | Surj cond | yes surj with _divMod_ (o + Fin.toℕ x + Fin.toℕ y) b {fromWitnessFalse (>⇒≢ (Surjective⇒b≥1 surj))}
-- toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | Surj cond | yes surj | result quotient remainder property div-eq mod-eq
--     rewrite div-eq | mod-eq =
--     begin
--         toℕ (inject≤ remainder d≥b ∷ n+ quotient ({! xs  !} ⊹ {!   !}))
--     -- ≡⟨ {!   !} ⟩
--         -- o + Fin.toℕ (inject≤ {! remainder  !} {!   !}) + {!   !} * b
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ∎
--     where   d≥b : d ≥ b
--             d≥b = Surjective⇒d≥b surj
-- toℕ-⊹-homo xs ys | Surj x | no ¬p = {!   !}
-- toℕ-⊹-homo xs ys | NonSurj x = {!   !}



-- toℕ-⊹-homo : ∀ {b d o}
--     → {surj : True (Surjective? b d o)}
--     → (xs ys : Num b d o)
--     → toℕ (_⊹_ {surj = surj} xs ys) ≡ toℕ xs + toℕ ys
-- -- toℕ-⊹-homo  {b} {d} {o} {f} xs       ys        = {!   !}
-- toℕ-⊹-homo  {b} {d} {o} xs       ys        with Surjective? b d o
-- toℕ-⊹-homo             ∙        ∙        | yes surj = refl
-- toℕ-⊹-homo             ∙        (y ∷ ys) | yes surj = refl
-- toℕ-⊹-homo             (x ∷ xs) ∙        | yes surj = sym (+-right-identity (toℕ (x ∷ xs)))
-- toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | yes surj with _divMod_ (o + Fin.toℕ x + Fin.toℕ y) b {fromWitnessFalse (>⇒≢ (Surjective⇒b≥1 surj))}
-- toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq =
--     {!   !}
-- -- toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq with surjectionView b d o
-- -- toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq | Surj condition with Surjective? b d o
-- -- toℕ-⊹-homo (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq | Surj condition | yes p =
-- --     begin
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         toℕ {!   !} + toℕ {!   !}
-- --     ∎
-- -- toℕ-⊹-homo (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq | Surj condition | no ¬p = {!   !}
-- -- toℕ-⊹-homo (x₁ ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq | NonSurj reason = contradiction surj (NonSurjCond⇏Surjective reason)
--     -- begin
--     --     toℕ {! x ∷ xs ⊹ ?  !}
--     -- ≡⟨ {!   !} ⟩
--     --     {!   !}
--     -- ≡⟨ {!   !} ⟩
--     --     {!   !}
--     -- ≡⟨ {!   !} ⟩
--     --     {!   !}
--     -- ≡⟨ {!   !} ⟩
--     --     toℕ {!   !} + toℕ {!   !}
--     -- ∎
-- -- toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | yes surj =
-- --     begin
-- --         toℕ {! x ∷ xs ⊹ ?  !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         toℕ {!   !} + toℕ {!   !}
-- --     ∎
-- toℕ-⊹-homo {surj = ()} xs ys | no _





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
