module Data.Num.Properties where

open import Data.Num
open import Data.Num.Core
open import Data.Num.Next

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin.Properties hiding (setoid; _≟_)
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

toℕ-⊹-ℤₙ-homo : ∀ {o}
    → (xs ys : Num 1 1 o)
    → ⟦ ⊹-ℤₙ xs ys ⟧ ≡ ⟦ xs ⟧ + ⟦ ys ⟧
toℕ-⊹-ℤₙ-homo {o} (x ∙) ys =
    begin
        Digit-toℕ x o + ⟦ ys ⟧ * 1
    ≡⟨ cong (_+_ (Digit-toℕ x o)) (*-right-identity ⟦ ys ⟧) ⟩
        Digit-toℕ x o + ⟦ ys ⟧
    ∎
toℕ-⊹-ℤₙ-homo {o} (x ∷ xs) ys =
    begin
        Digit-toℕ x o + ⟦ ⊹-ℤₙ xs ys ⟧ * 1
    ≡⟨ cong (λ w → Digit-toℕ x o + w * 1) (toℕ-⊹-ℤₙ-homo xs ys) ⟩
        Digit-toℕ x o + (⟦ xs ⟧ + ⟦ ys ⟧) * 1
    ≡⟨ cong (_+_ (Digit-toℕ x o)) (distribʳ-*-+ 1 ⟦ xs ⟧ ⟦ ys ⟧) ⟩
        Digit-toℕ x o + (⟦ xs ⟧ * 1 + ⟦ ys ⟧ * 1)
    ≡⟨ cong (λ w → Digit-toℕ x o + (⟦ xs ⟧ * 1 + w)) (*-right-identity ⟦ ys ⟧) ⟩
        Digit-toℕ x o + (⟦ xs ⟧ * 1 + ⟦ ys ⟧)
    ≡⟨ sym (+-assoc (Digit-toℕ x o) (⟦ xs ⟧ * 1) ⟦ ys ⟧) ⟩
        Digit-toℕ x o + ⟦ xs ⟧ * 1 + ⟦ ys ⟧
    ∎

toℕ-⊹-Proper-homo : ∀ {b d o}
    → (¬gapped : (1 ⊔ o) * suc b ≤ suc d)
    → (proper : suc d + o ≥ 2)
    → (xs ys : Num (suc b) (suc d) o)
    →  ⟦ ⊹-Proper ¬gapped proper xs ys ⟧ ≡ ⟦ xs ⟧ + ⟦ ys ⟧
toℕ-⊹-Proper-homo {b} {d} {o} ¬gapped proper (x ∙) ys = n+-Proper-toℕ ¬gapped proper x ys
toℕ-⊹-Proper-homo {b} {d} {o} ¬gapped proper (x ∷ xs) (y ∙) =
    begin
        ⟦ n+-Proper ¬gapped proper y (x ∷ xs) ⟧
    ≡⟨ n+-Proper-toℕ ¬gapped proper y (x ∷ xs) ⟩
        Digit-toℕ y o + (Digit-toℕ x o + ⟦ xs ⟧ * suc b)
    ≡⟨ +-comm (Digit-toℕ y o) (Digit-toℕ x o + ⟦ xs ⟧ * suc b) ⟩
        Digit-toℕ x o + ⟦ xs ⟧ * suc b + Digit-toℕ y o
    ∎
toℕ-⊹-Proper-homo {b} {d} {o} ¬gapped proper (x ∷ xs) (y ∷ ys) with sumView b d o ¬gapped proper x y
toℕ-⊹-Proper-homo {b} {d} {o} ¬gapped proper (x ∷ xs) (y ∷ ys) | Below leftover property =
    begin
        Digit-toℕ leftover o + ⟦ ⊹-Proper ¬gapped proper xs ys ⟧ * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + w * suc b) (toℕ-⊹-Proper-homo ¬gapped proper xs ys) ⟩
        Digit-toℕ leftover o + (⟦ xs ⟧ + ⟦ ys ⟧) * suc b
    ≡⟨ cong (λ w → w + (⟦ xs ⟧ + ⟦ ys ⟧) * suc b) property ⟩
        Digit-toℕ x o + (Digit-toℕ y o) + (⟦ xs ⟧ + ⟦ ys ⟧) * suc b
    ≡⟨ cong (λ w → Digit-toℕ x o + (Digit-toℕ y o) + w) (distribʳ-*-+ (suc b) ⟦ xs ⟧ ⟦ ys ⟧) ⟩
        (Digit-toℕ x o) + (Digit-toℕ y o) + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b)
    ≡⟨ +-assoc (Digit-toℕ x o) (Digit-toℕ y o) (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b) ⟩
        Digit-toℕ x o + (Digit-toℕ y o + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b))
    ≡⟨ cong (λ w → Digit-toℕ x o + w) (a+[b+c]≡b+[a+c] (Digit-toℕ y o) (⟦ xs ⟧ * suc b) (⟦ ys ⟧ * suc b)) ⟩
        Digit-toℕ x o + (⟦ xs ⟧ * suc b + (Digit-toℕ y o + ⟦ ys ⟧ * suc b))
    ≡⟨ sym (+-assoc (Digit-toℕ x o) (⟦ xs ⟧ * suc b) (Digit-toℕ y o + ⟦ ys ⟧ * suc b)) ⟩
        Digit-toℕ x o + ⟦ xs ⟧ * suc b + (Digit-toℕ y o + ⟦ ys ⟧ * suc b)
    ∎
toℕ-⊹-Proper-homo {b} {d} {o} ¬gapped proper (x ∷ xs) (y ∷ ys) | Within leftover carry property =
    begin
        Digit-toℕ leftover o + ⟦ n+-Proper ¬gapped proper carry (⊹-Proper ¬gapped proper xs ys) ⟧ * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + w * suc b) (n+-Proper-toℕ ¬gapped proper carry (⊹-Proper ¬gapped proper xs ys))   ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o + ⟦ ⊹-Proper ¬gapped proper xs ys ⟧) * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + (Digit-toℕ carry o + w) * suc b) (toℕ-⊹-Proper-homo ¬gapped proper xs ys) ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o + (⟦ xs ⟧ + ⟦ ys ⟧)) * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + w) (distribʳ-*-+ (suc b) (Digit-toℕ carry o) (⟦ xs ⟧ + ⟦ ys ⟧)) ⟩
        Digit-toℕ leftover o + ((Digit-toℕ carry o) * suc b + (⟦ xs ⟧ + ⟦ ys ⟧) * suc b)
    ≡⟨ cong (λ w → Digit-toℕ leftover o + ((Digit-toℕ carry o) * suc b + w)) (distribʳ-*-+ (suc b) ⟦ xs ⟧ ⟦ ys ⟧) ⟩
        Digit-toℕ leftover o + ((Digit-toℕ carry o) * suc b + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b))
    ≡⟨ sym (+-assoc (Digit-toℕ leftover o) ((Digit-toℕ carry o) * suc b) (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b)) ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o) * suc b + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b)
    ≡⟨ cong (λ w → w + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b)) property ⟩
        (Digit-toℕ x o) + (Digit-toℕ y o) + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b)
    ≡⟨ +-assoc (Digit-toℕ x o) (Digit-toℕ y o) (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b) ⟩
        Digit-toℕ x o + (Digit-toℕ y o + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b))
    ≡⟨ cong (λ w → Digit-toℕ x o + w) (a+[b+c]≡b+[a+c] (Digit-toℕ y o) (⟦ xs ⟧ * suc b) (⟦ ys ⟧ * suc b)) ⟩
        Digit-toℕ x o + (⟦ xs ⟧ * suc b + (Digit-toℕ y o + ⟦ ys ⟧ * suc b))
    ≡⟨ sym (+-assoc (Digit-toℕ x o) (⟦ xs ⟧ * suc b) (Digit-toℕ y o + ⟦ ys ⟧ * suc b)) ⟩
        Digit-toℕ x o + ⟦ xs ⟧ * suc b + (Digit-toℕ y o + ⟦ ys ⟧ * suc b)
    ∎
toℕ-⊹-Proper-homo {b} {d} {o} ¬gapped proper (x ∷ xs) (y ∷ ys) | Above leftover carry property =
    begin
        Digit-toℕ leftover o + ⟦ n+-Proper ¬gapped proper carry (⊹-Proper ¬gapped proper xs ys) ⟧ * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + w * suc b) (n+-Proper-toℕ ¬gapped proper carry (⊹-Proper ¬gapped proper xs ys))   ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o + ⟦ ⊹-Proper ¬gapped proper xs ys ⟧) * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + (Digit-toℕ carry o + w) * suc b) (toℕ-⊹-Proper-homo ¬gapped proper xs ys) ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o + (⟦ xs ⟧ + ⟦ ys ⟧)) * suc b
    ≡⟨ cong (λ w → Digit-toℕ leftover o + w) (distribʳ-*-+ (suc b) (Digit-toℕ carry o) (⟦ xs ⟧ + ⟦ ys ⟧)) ⟩
        Digit-toℕ leftover o + ((Digit-toℕ carry o) * suc b + (⟦ xs ⟧ + ⟦ ys ⟧) * suc b)
    ≡⟨ cong (λ w → Digit-toℕ leftover o + ((Digit-toℕ carry o) * suc b + w)) (distribʳ-*-+ (suc b) ⟦ xs ⟧ ⟦ ys ⟧) ⟩
        Digit-toℕ leftover o + ((Digit-toℕ carry o) * suc b + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b))
    ≡⟨ sym (+-assoc (Digit-toℕ leftover o) ((Digit-toℕ carry o) * suc b) (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b)) ⟩
        Digit-toℕ leftover o + (Digit-toℕ carry o) * suc b + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b)
    ≡⟨ cong (λ w → w + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b)) property ⟩
        (Digit-toℕ x o) + (Digit-toℕ y o) + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b)
    ≡⟨ +-assoc (Digit-toℕ x o) (Digit-toℕ y o) (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b) ⟩
        Digit-toℕ x o + (Digit-toℕ y o + (⟦ xs ⟧ * suc b + ⟦ ys ⟧ * suc b))
    ≡⟨ cong (λ w → Digit-toℕ x o + w) (a+[b+c]≡b+[a+c] (Digit-toℕ y o) (⟦ xs ⟧ * suc b) (⟦ ys ⟧ * suc b)) ⟩
        Digit-toℕ x o + (⟦ xs ⟧ * suc b + (Digit-toℕ y o + ⟦ ys ⟧ * suc b))
    ≡⟨ sym (+-assoc (Digit-toℕ x o) (⟦ xs ⟧ * suc b) (Digit-toℕ y o + ⟦ ys ⟧ * suc b)) ⟩
        Digit-toℕ x o + ⟦ xs ⟧ * suc b + (Digit-toℕ y o + ⟦ ys ⟧ * suc b)
    ∎


-- _⊹_ : ∀ {b d o}
--     → {cond : N+Closed b d o}
--     → (xs ys : Num b d o)
--     → Num b d o
-- _⊹_ {b} {d} {o} {IsContinuous cont} xs ys with numView b d o
-- _⊹_ {cond = IsContinuous ()} xs ys | NullBase d o
-- _⊹_ {cond = IsContinuous cont} xs ys | NoDigits b o = NoDigits-explode xs
-- _⊹_ {cond = IsContinuous ()} xs ys | AllZeros b
-- _⊹_ {cond = IsContinuous cont} xs ys | Proper b d o proper with Gapped#0? b d o
-- _⊹_ {cond = IsContinuous ()} xs ys | Proper b d o proper | yes ¬gapped#0
-- _⊹_ {cond = IsContinuous cont} xs ys | Proper b d o proper | no ¬gapped#0 = ⊹-Proper (≤-pred (≰⇒> ¬gapped#0)) proper xs ys
-- _⊹_ {cond = ℤₙ} xs ys = ⊹-ℤₙ xs ys

toℕ-⊹-homo : ∀ {b d o}
    → (cond : N+Closed b d o)
    → (xs ys : Num b d o)
    → ⟦ _⊹_ {cond = cond} xs ys ⟧ ≡ ⟦ xs ⟧ + ⟦ ys ⟧
toℕ-⊹-homo {b} {d} {o} (IsContinuous cont) xs ys with numView b d o
toℕ-⊹-homo (IsContinuous ()) xs ys | NullBase d o
toℕ-⊹-homo (IsContinuous cont) xs ys | NoDigits b o = NoDigits-explode xs
toℕ-⊹-homo (IsContinuous ()) xs ys | AllZeros b
toℕ-⊹-homo (IsContinuous cont) xs ys | Proper b d o proper with Gapped#0? b d o
toℕ-⊹-homo (IsContinuous ()) xs ys | Proper b d o proper | yes gapped#0
toℕ-⊹-homo (IsContinuous cont) xs ys | Proper b d o proper | no ¬gapped#0 = toℕ-⊹-Proper-homo (≤-pred (≰⇒> ¬gapped#0)) proper xs ys
toℕ-⊹-homo ℤₙ xs ys = toℕ-⊹-ℤₙ-homo xs ys

-- toℕ-≋-ℕ⇒Num-lemma-1 : ∀ m n → m * suc n ≡ 0 → m ≡ 0
-- toℕ-≋-ℕ⇒Num-lemma-1 zero n p = refl
-- toℕ-≋-ℕ⇒Num-lemma-1 (suc m) n ()
--
--
-- toℕ-≋-ℕ⇒Num-lemma-2 : ∀ m n → m ≢ 0 → m + n ≢ 0
-- toℕ-≋-ℕ⇒Num-lemma-2 zero    n p = contradiction refl p
-- toℕ-≋-ℕ⇒Num-lemma-2 (suc m) n p ()
--
-- toℕ-≋-ℕ⇒Num : ∀ {b d o}
--     → (xs ys : Num b d o)
--     → toℕ xs ≡ toℕ ys
--     → xs ≋ ys
-- toℕ-≋-ℕ⇒Num ∙ ∙        ⟦xs⟧≡⟦ys⟧ = tt
-- toℕ-≋-ℕ⇒Num {b} {zero} ∙ (() ∷ ys) ⟦∙⟧≡⟦y∷ys⟧
-- toℕ-≋-ℕ⇒Num {b} {suc d} {o} ∙ (y ∷ ys) ⟦∙⟧≡⟦y∷ys⟧ with Digit-toℕ y o ≟ 0
-- toℕ-≋-ℕ⇒Num {zero} {suc d} ∙ (y ∷ ys) ⟦∙⟧≡⟦y∷ys⟧ | yes p = tt
-- toℕ-≋-ℕ⇒Num {suc b} {suc d} {o} ∙ (y ∷ ys) ⟦∙⟧≡⟦y∷ys⟧ | yes p =
--     let ⟦ys⟧≡0 : toℕ ys * suc b ≡ 0
--         ⟦ys⟧≡0 =
--             begin
--                 toℕ ys * suc b
--             ≡⟨ cong (λ w → w + toℕ ys * suc b) (sym p) ⟩
--                 o + Fin.toℕ y + toℕ ys * suc b
--             ≡⟨ sym ⟦∙⟧≡⟦y∷ys⟧ ⟩
--                 zero
--             ∎
--     in
--     toℕ-≋-ℕ⇒Num ∙ ys (sym (toℕ-≋-ℕ⇒Num-lemma-1 (toℕ ys) b ⟦ys⟧≡0))
-- toℕ-≋-ℕ⇒Num {b} {suc d} {o} ∙ (y ∷ ys) ⟦∙⟧≡⟦y∷ys⟧ | no ¬p = toℕ-≋-ℕ⇒Num-lemma-2 (Digit-toℕ y o) (toℕ ys * b) ¬p (sym ⟦∙⟧≡⟦y∷ys⟧)
-- toℕ-≋-ℕ⇒Num {b} {zero} (() ∷ xs) ∙ ⟦x∷xs⟧≡⟦∙⟧
-- toℕ-≋-ℕ⇒Num {b} {suc d} {o} (x ∷ xs) ∙ ⟦x∷xs⟧≡⟦∙⟧ with Digit-toℕ x o ≟ 0
-- toℕ-≋-ℕ⇒Num {zero} {suc d} (x ∷ xs) ∙ ⟦x∷xs⟧≡⟦∙⟧ | yes p = tt
-- toℕ-≋-ℕ⇒Num {suc b} {suc d} (x ∷ xs) ∙ ⟦x∷xs⟧≡⟦∙⟧ | yes p = {!   !}
-- toℕ-≋-ℕ⇒Num {b} {suc d} (x ∷ xs) ∙ ⟦x∷xs⟧≡⟦∙⟧ | no ¬p = {!   !}
-- toℕ-≋-ℕ⇒Num (x ∷ xs) (x₁ ∷ ys) ⟦xs⟧≡⟦ys⟧ = {!   !}


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
