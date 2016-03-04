module Data.Num.Bijective.Properties where

open import Data.Num.Bijective

open import Data.Nat
open import Data.Fin as Fin using ()
open import Data.Fin.Properties hiding (_≟_)
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; sym; trans; inspect)
open PropEq.≡-Reasoning
    renaming (begin_ to beginEq_; _≡⟨_⟩_ to _≡Eq⟨_⟩_; _∎ to _∎Eq)
open import Induction.Nat
open import Induction.WellFounded
open import Induction

--
--      xs ── +1 ──➞ xs'
--      |              |
--     toℕ           toℕ
--      ↓              ↓
--      n ── suc ─➞ suc n
--
+1-toℕ-suc : ∀ b xs → toℕ {suc b} (+1 xs) ≡ suc (toℕ xs)
+1-toℕ-suc b ∙ = refl
+1-toℕ-suc b ([ x ] xs) with Fin.toℕ x ≟ b
+1-toℕ-suc b ([ x ] xs) | yes p =
    beginEq
        toℕ ([ Fin.zero ] +1 xs)
    ≡Eq⟨ cong (λ w → suc (w * suc b)) (+1-toℕ-suc b xs) ⟩
        suc (suc (b + toℕ xs * suc b))
    ≡Eq⟨ cong (λ w → suc (suc (w + toℕ xs * suc b))) (sym p) ⟩
        suc (toℕ ([ x ] xs))
    ∎Eq
+1-toℕ-suc b ([ x ] xs) | no ¬p =
    cong (λ w → suc w + toℕ xs * suc b) (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p)))

+1-never-∙ : ∀ {b} xs → +1 {b} xs ≢ ∙
+1-never-∙ ∙ ()
+1-never-∙ {b} ([ x ] xs) +1xs≡∙ with Fin.toℕ x ≟ b
+1-never-∙ ([ x ] xs) () | yes p
+1-never-∙ ([ x ] xs) () | no ¬p

fromℕ-∙-0 : ∀ {b} n → fromℕ {b} n ≡ ∙ → n ≡ 0
fromℕ-∙-0 zero    p = refl
fromℕ-∙-0 (suc n) p = contradiction p (+1-never-∙ (fromℕ n))


--
--      n ── fromℕ ─➞ xs ── toℕ ─➞ n
--
toℕ-fromℕ : ∀ b n → toℕ {suc b} (fromℕ {b} n) ≡ n
toℕ-fromℕ b zero = refl
toℕ-fromℕ b (suc n)  with fromℕ {b} n | inspect (fromℕ {b}) n
toℕ-fromℕ b (suc n) | ∙ | PropEq.[ eq ] = cong suc (sym (fromℕ-∙-0 n eq))
toℕ-fromℕ b (suc n) | [ x ] xs | PropEq.[ eq ] with Fin.toℕ x ≟ b
toℕ-fromℕ b (suc n) | [ x ] xs | PropEq.[ eq ] | yes p =
    beginEq
        toℕ ([ Fin.zero ] +1 xs)
    ≡Eq⟨ refl ⟩
        suc (toℕ (+1 xs) * suc b)
    ≡Eq⟨ cong (λ w → suc (w * suc b)) (+1-toℕ-suc b xs) ⟩
        suc (suc (b + toℕ xs * suc b))
    ≡Eq⟨ cong (λ w → suc (suc (w + toℕ xs * suc b))) (sym p) ⟩
        suc (suc (Fin.toℕ x) + toℕ xs * suc b)
    ≡Eq⟨ cong (λ w → suc (toℕ w)) (sym eq) ⟩
        suc (toℕ (fromℕ n))
    ≡Eq⟨ cong suc (toℕ-fromℕ b n) ⟩
        suc n
    ∎Eq
toℕ-fromℕ b (suc n) | [ x ] xs | PropEq.[ eq ] | no ¬p =
    beginEq
        toℕ ([ digit+1 x ¬p ] xs)
    ≡Eq⟨ cong (λ w → suc (w + toℕ xs * suc b)) (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p))) ⟩
        suc (suc (Fin.toℕ x + toℕ xs * suc b))
    ≡Eq⟨ cong (λ w → suc (toℕ w)) (sym eq) ⟩
        suc (toℕ (fromℕ n))
    ≡Eq⟨ cong suc (toℕ-fromℕ b n) ⟩
        suc n
    ∎Eq


-- beginEq
--     {!   !}
-- ≡Eq⟨ {!   !} ⟩
--     {!   !}
-- ≡Eq⟨ {!   !} ⟩
--     {!   !}
-- ≡Eq⟨ {!   !} ⟩
--     {!   !}
-- ≡Eq⟨ {!   !} ⟩
--     {!   !}
-- ∎Eq


postulate
    toℕ-add-hom : ∀ {b} (xs ys : Num b) → toℕ (add xs ys) ≡ toℕ xs + toℕ ys
--
--
-- open import Data.Nat.DivMod
-- open import Data.Nat.Properties.Simple
--
-- add-comm : ∀ {b} → (xs ys : Num b) → add xs ys ≡ add ys xs
-- add-comm ∙          ∙ = refl
-- add-comm ∙          ([ y ] ys) = refl
-- add-comm ([ x ] xs) ∙ = refl
-- add-comm {zero} ([ () ] xs) ([ () ] ys)
-- add-comm {suc b} ([ x ] xs) ([ y ] ys) with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b) | (suc (Fin.toℕ y + Fin.toℕ x)) divMod (suc b)
-- add-comm {suc b} ([ x ] xs) ([ y ] ys) | result zero R prop | result zero R' prop' =
--     beginEq
--         ([ R ] add xs ys)
--     ≡Eq⟨ cong (λ w → [ w ] add xs ys) (toℕ-injective (
--         beginEq
--             Fin.toℕ R
--         ≡Eq⟨ sym (+-right-identity (Fin.toℕ R)) ⟩
--             Fin.toℕ R + zero
--         ≡Eq⟨ sym prop ⟩
--             suc (Fin.toℕ x + Fin.toℕ y)
--         ≡Eq⟨ cong suc (+-comm (Fin.toℕ x) (Fin.toℕ y)) ⟩
--             suc (Fin.toℕ y + Fin.toℕ x)
--         ≡Eq⟨ prop' ⟩
--             Fin.toℕ R' + zero
--         ≡Eq⟨ +-right-identity (Fin.toℕ R') ⟩
--             Fin.toℕ R'
--         ∎Eq
--     ))⟩
--         ([ R' ] add xs ys)
--     ≡Eq⟨ cong (λ w → [ R' ] w) (add-comm {suc b} xs ys) ⟩
--         ([ R' ] add ys xs)
--     ∎Eq
-- add-comm {suc b} ([ x ] xs) ([ y ] ys) | result zero R prop | result (suc Q') R' prop' = {!   !}
-- add-comm {suc b} ([ x ] xs) ([ y ] ys) | result (suc Q) R prop | result Q' R' prop' = {!   !}
-- -- add-comm {suc b} ([ x ] xs) ([ y ] ys) with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b)
-- -- add-comm {suc b} ([ x ] xs) ([ y ] ys) | result zero R prop =
-- --     beginEq
-- --         add ([ x ] xs) ([ y ] ys)
-- --     ≡Eq⟨ refl ⟩
-- --         add ([ x ] xs) ([ y ] ys)
-- --     ≡Eq⟨ refl ⟩
-- --         add ([ x ] xs) ([ y ] ys)
-- --     ≡Eq⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡Eq⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡Eq⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡Eq⟨ {!   !} ⟩
-- --         add ([ y ] ys) ([ x ] xs)
-- --     ∎Eq
-- -- add-comm ([ x ] xs) ([ y ] ys) | result (suc Q) R prop = {!   !}
-- --     -- where
