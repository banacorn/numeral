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
    → {surj : True (Surjective? b d o)}
    → (xs ys : Num b d o)
    → toℕ (_⊹_ {surj = surj} xs ys) ≡ toℕ xs + toℕ ys
toℕ-⊹-homo {b} {d} {o} xs ys with Surjective? b d o
toℕ-⊹-homo             ∙        ∙        | yes surj = refl
toℕ-⊹-homo             ∙        (y ∷ ys) | yes surj = refl
toℕ-⊹-homo             (x ∷ xs) ∙        | yes surj = sym (+-right-identity (toℕ (x ∷ xs)))
toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | yes surj with _divMod_ (o + Fin.toℕ x + Fin.toℕ y) b {fromWitnessFalse (>⇒≢ (Surjective⇒b≥1 surj))}
toℕ-⊹-homo {b} {d} {o} (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq =
    begin
        toℕ (inject≤ remainder d≥b ∷ n+ quotient (_⊹_ {surj = fromWitness surj} xs ys))
    ≡⟨ refl ⟩
        Digit-toℕ (inject≤ remainder d≥b) o + toℕ (n+ quotient (_⊹_ {surj = fromWitness surj} xs ys)) * b
    -- cancel  `toℕ (n+ ...)`
    ≡⟨ cong (λ w → Digit-toℕ (inject≤ remainder d≥b) o + w * b) (toℕ-n+ {isSurj = Surjective⇒IsSurj surj} quotient (_⊹_ {surj = fromWitness surj} xs ys)) ⟩
        Digit-toℕ (inject≤ remainder d≥b) o + (quotient + toℕ (_⊹_ {surj = fromWitness surj} xs ys)) * b
    -- cancel  `toℕ (... ⊹ ...)`
    ≡⟨ cong (λ w → Digit-toℕ (inject≤ remainder d≥b) o + (quotient + w) * b) (toℕ-⊹-homo {surj = fromWitness surj} xs ys) ⟩
        Digit-toℕ (inject≤ remainder d≥b) o + (quotient + (toℕ xs + toℕ ys)) * b
    -- cancel   `Fin.toℕ (inject≤ ...)`
    ≡⟨ cong ((λ w → o + w + (quotient + (toℕ xs + toℕ ys)) * b)) (inject≤-lemma remainder d≥b) ⟩
        o + Fin.toℕ remainder + (quotient + (toℕ xs + toℕ ys)) * b

    -- get `Fin.toℕ remainder + quotient * b` for `property`
    ≡⟨ cong (λ w → o + Fin.toℕ remainder + w) (distribʳ-*-+ b quotient (toℕ xs + toℕ ys)) ⟩
        o + Fin.toℕ remainder + (quotient * b + (toℕ xs + toℕ ys) * b)
    ≡⟨ +-assoc o (Fin.toℕ remainder) (quotient * b + (toℕ xs + toℕ ys) * b) ⟩
        o + ((Fin.toℕ remainder) + (quotient * b + (toℕ xs + toℕ ys) * b))
    ≡⟨ cong (λ w → o + w) (sym (+-assoc (Fin.toℕ remainder) (quotient * b) ((toℕ xs + toℕ ys) * b))) ⟩
        o + (Fin.toℕ remainder + quotient * b + (toℕ xs + toℕ ys) * b)

    -- apply    `property`
    ≡⟨ cong (λ w → o + (w + (toℕ xs + toℕ ys) * b)) (sym property) ⟩
        o + ((o + Fin.toℕ x) + Fin.toℕ y + (toℕ xs + toℕ ys) * b)

    ≡⟨ cong (λ w → o + ((o + Fin.toℕ x) + Fin.toℕ y + w)) (distribʳ-*-+ b (toℕ xs) (toℕ ys)) ⟩
        o + ((o + Fin.toℕ x + Fin.toℕ y) + (toℕ xs * b + toℕ ys * b))
    ≡⟨ cong (λ w → o + w) ([a+b]+c≡[a+c]+b (o + Fin.toℕ x) (Fin.toℕ y) (toℕ xs * b + toℕ ys * b)) ⟩
        o + (o + Fin.toℕ x + (toℕ xs * b + toℕ ys * b) + Fin.toℕ y)
    ≡⟨ cong (λ w → o + (w + Fin.toℕ y)) (sym (+-assoc (o + Fin.toℕ x) (toℕ xs * b) (toℕ ys * b))) ⟩
        o + ((o + Fin.toℕ x + toℕ xs * b) + toℕ ys * b + Fin.toℕ y)
    ≡⟨ cong (λ w → o + w) (+-assoc (o + Fin.toℕ x + toℕ xs * b) (toℕ ys * b) (Fin.toℕ y)) ⟩
        o + (o + Fin.toℕ x + toℕ xs * b + (toℕ ys * b + Fin.toℕ y))
    ≡⟨ a+[b+c]≡b+[a+c] o (o + Fin.toℕ x + toℕ xs * b) (toℕ ys * b + Fin.toℕ y) ⟩
        (o + Fin.toℕ x + toℕ xs * b) + (o + (toℕ ys * b + Fin.toℕ y))
    ≡⟨ cong (λ w → (Digit-toℕ x o + toℕ xs * b) + (o + w)) (+-comm (toℕ ys * b) (Fin.toℕ y)) ⟩
        o + Fin.toℕ x + toℕ xs * b + (o + (Fin.toℕ y + toℕ ys * b))
    ≡⟨ cong (λ w → (Digit-toℕ x o + toℕ xs * b) + w) (sym (+-assoc o (Fin.toℕ y) (toℕ ys * b))) ⟩
        (Digit-toℕ x o + toℕ xs * b) + (Digit-toℕ y o + toℕ ys * b)
    ∎
    where   d≥b : d ≥ b
            d≥b = Surjective⇒d≥b surj
toℕ-⊹-homo {surj = ()} xs ys | no _

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
