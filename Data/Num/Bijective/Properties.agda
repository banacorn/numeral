module Data.Num.Bijective.Properties where

open import Data.Num.Bijective

open import Data.Nat
open import Data.Fin as Fin using ()
open import Data.Fin.Properties using (bounded; toℕ-fromℕ≤)
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
toℕ∘fromℕ=id : ∀ b n → toℕ {suc b} (fromℕ {b} n) ≡ n
toℕ∘fromℕ=id b zero = refl
toℕ∘fromℕ=id b (suc n)  with fromℕ {b} n | inspect (fromℕ {b}) n
toℕ∘fromℕ=id b (suc n) | ∙ | PropEq.[ eq ] = cong suc (sym (fromℕ-∙-0 n eq))
toℕ∘fromℕ=id b (suc n) | [ x ] xs | PropEq.[ eq ] with Fin.toℕ x ≟ b
toℕ∘fromℕ=id b (suc n) | [ x ] xs | PropEq.[ eq ] | yes p =
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
    ≡Eq⟨ cong suc (toℕ∘fromℕ=id b n) ⟩
        suc n
    ∎Eq
toℕ∘fromℕ=id b (suc n) | [ x ] xs | PropEq.[ eq ] | no ¬p =
    beginEq
        toℕ ([ digit+1 x ¬p ] xs)
    ≡Eq⟨ cong (λ w → suc (w + toℕ xs * suc b)) (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p))) ⟩
        suc (suc (Fin.toℕ x + toℕ xs * suc b))
    ≡Eq⟨ cong (λ w → suc (toℕ w)) (sym eq) ⟩
        suc (toℕ (fromℕ n))
    ≡Eq⟨ cong suc (toℕ∘fromℕ=id b n) ⟩
        suc n
    ∎Eq
