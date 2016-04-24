module Data.Num.Injection where

open import Data.Num.Core

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra

open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Data.Fin.Properties
    using (toℕ-fromℕ≤; bounded; inject≤-lemma)
    renaming (toℕ-injective to Fin→ℕ-injective; _≟_ to _Fin≟_)
open import Data.Fin.Properties.Extra
open import Data.Product
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)


open import Function
open import Function.Injection
open Injection
-- open import Function.Equality using (_⟶_; _⟨$⟩_)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)


record InjCond (b d o : ℕ) : Set where
    constructor bijCond
    field
        b≥d: : b ≥ d
        o≥1: : o ≥ 1
open InjCond public

data NonInjCond : ℕ → ℕ → ℕ → Set where
    d>b: : ∀ {b d o} → (d>b : d > b) → NonInjCond b d o  -- having more digits than the base
    o≡0: : ∀ {b d o} → (o≡0 : o ≡ 0) → NonInjCond b d 0 -- leading zeroes


data InjectionView : ℕ → ℕ → ℕ → Set where
    Inj    : ∀ {b d o} → InjCond    b d o → InjectionView b d o
    NonInj : ∀ {b d o} → NonInjCond b d o → InjectionView b d o


injectionView : (b d o : ℕ) → InjectionView b d o
injectionView b d zero    = NonInj (o≡0: refl)
injectionView b d (suc o) with d ≤? b
injectionView b d (suc o) | yes p = Inj (bijCond p (s≤s z≤n))
injectionView b d (suc o) | no ¬p = NonInj (d>b: (≰⇒> ¬p))

IsInjective : ℕ → ℕ → ℕ → Set
IsInjective b d o with injectionView b d o
IsInjective b d o | Inj    x = ⊤
IsInjective b d o | NonInj x = ⊥

InjCond⇒IsInj : ∀ {b d o} → InjCond b d o → IsInjective b d o
InjCond⇒IsInj {b} {d} {o} cond with injectionView b d o
InjCond⇒IsInj cond               | Inj _ = tt
InjCond⇒IsInj (bijCond b≥d o≥1) | NonInj (d>b: d>b) = contradiction b≥d (>⇒≰ d>b)
InjCond⇒IsInj (bijCond b≥d () ) | NonInj (o≡0: refl)

NonInjCond⇏IsInj : ∀ {b d o} → NonInjCond b d o → ¬ IsInjective b d o
NonInjCond⇏IsInj {b} {d} {o} reason claim with injectionView b d o
NonInjCond⇏IsInj (d>b: d>b) claim | Inj (bijCond b≥d o≥1) = contradiction b≥d (>⇒≰ d>b)
NonInjCond⇏IsInj (o≡0: o≡0) claim | Inj (bijCond b≥d ())
NonInjCond⇏IsInj reason     ()    | NonInj _

-- For cases of ⟦x∷xs⟧ ≡ ⟦y∷∙⟧
toℕ-injective-⟦x∷xs⟧-⟦y∷∙⟧-lemma : ∀ {b d o} (x y : Fin d) (xs : ℕ)
    → InjCond b d o
    → Digit-toℕ x o + suc xs * b > Digit-toℕ y o + zero
toℕ-injective-⟦x∷xs⟧-⟦y∷∙⟧-lemma {b} {d} {o} x y xs cond =
    start
        -- move `o` to the left
        suc (o + Fin.toℕ y + zero)
    ≈⟨ +-right-identity (suc (o + Fin.toℕ y)) ⟩
        suc (o + Fin.toℕ y)
    ≈⟨ sym (+-suc o (Fin.toℕ y)) ⟩

        -- proof that `suc (Fin.toℕ y) ≤ Fin.toℕ x + suc xs * suc b`
        o + suc (Fin.toℕ y)
    ≤⟨ n+-mono o $ start
            suc (Fin.toℕ y)
        ≤⟨ bounded y ⟩
            d
        ≤⟨ b≥d: cond ⟩
            b
        ≈⟨ sym (*-left-identity b) ⟩
            1 * b
        ≤⟨ _*-mono_ {1} {suc xs} {b} {b} (s≤s z≤n) ≤-refl ⟩
            suc xs * b
        ≤⟨ n≤m+n (Fin.toℕ x) (suc xs * b) ⟩
            Fin.toℕ x + suc xs * b
        □
     ⟩
        o + (Fin.toℕ x + suc xs * b)
    ≈⟨ sym (+-assoc o (Fin.toℕ x) (suc xs * b)) ⟩
        o + Fin.toℕ x + suc xs * b
    □

-- generalized from toℕ (x ∷ xs) ≡ toℕ (y ∷ ys)
toℕ-injective-lemma : ∀ {b d o} (x y : Fin d) (xs ys : ℕ)
    → InjCond b d o
    → Digit-toℕ x o + xs * b ≡ Digit-toℕ y o + ys * b
    → x ≡ y × xs ≡ ys
toℕ-injective-lemma {b} {d} {o} x y zero     zero     cond eq
    = Fin→ℕ-injective              -- Fin.toℕ x         ⇒ x
        (cancel-+-left o            -- Digit-toℕ x o     ⇒ Fin.toℕ x
            (cancel-+-right 0 eq))  -- Digit-toℕ x o + 0 ⇒ Digit-toℕ x o
    , refl
toℕ-injective-lemma {b} {d} {o} x y zero     (suc ys) cond eq =
    contradiction eq $ <⇒≢ $ toℕ-injective-⟦x∷xs⟧-⟦y∷∙⟧-lemma y x ys cond
toℕ-injective-lemma {b} {d} {o} x y (suc xs) zero     cond eq =
    contradiction eq $ >⇒≢ $ toℕ-injective-⟦x∷xs⟧-⟦y∷∙⟧-lemma x y xs cond
toℕ-injective-lemma {b} {d} {o} x y (suc xs) (suc ys) cond eq
    = proj₁ ind
    , cong suc (proj₂ ind)
    where   ⟦x∷xs⟧≡⟦y∷ys⟧ : Digit-toℕ x o + xs * b ≡ Digit-toℕ y o + ys * b
            ⟦x∷xs⟧≡⟦y∷ys⟧ =
                -- 1. add a `b` to the left
                cancel-+-left b $ begin
                    b + (o + Fin.toℕ x + xs * b)
                -- 2. push `suc b` inward
                ≡⟨ a+[b+c]≡b+[a+c] b (o + Fin.toℕ x) (xs * b) ⟩
                    o + Fin.toℕ x + (b + xs * b)
                ≡⟨ eq ⟩
                    o + Fin.toℕ y + (b + ys * b)
                -- 3. pull `suc b` back
                ≡⟨ a+[b+c]≡b+[a+c] (o + Fin.toℕ y) b (ys * b) ⟩
                    b + (o + Fin.toℕ y + ys * b)
                ∎
            ind : x ≡ y × xs ≡ ys
            ind = toℕ-injective-lemma x y xs ys cond ⟦x∷xs⟧≡⟦y∷ys⟧

--


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
toℕ-injective : ∀ {b d o}
    → {isInj : IsInjective b d o}
    → (xs ys : Num b d o)
    → toℕ xs ≡ toℕ ys
    → xs ≡ ys
toℕ-injective {_} {_} {_}          ∙        ∙        eq = refl
toℕ-injective {_} {_} {zero } {()} ∙        (x ∷ ys) eq     -- o ≢ 0
toℕ-injective {_} {_} {suc o}      ∙        (x ∷ ys) ()
toℕ-injective {_} {_} {zero } {()} (x ∷ xs) ∙        eq     -- o ≢ 0
toℕ-injective {_} {_} {suc o}      (x ∷ xs) ∙        ()
toℕ-injective {b} {d} {o}     {pf} (x ∷ xs) (y ∷ ys) eq with injectionView b d o
toℕ-injective {b} {zero} (() ∷ xs) (y ∷ ys) eq | Inj condition
toℕ-injective {b} {suc d} {_} (x ∷ xs) (y ∷ ys) eq | Inj condition =
    cong₂ _∷_ (proj₁ x≡y×⟦xs⟧≡⟦ys⟧) xs≡ys
    where   x≡y×⟦xs⟧≡⟦ys⟧ : x ≡ y × toℕ xs ≡ toℕ ys
            x≡y×⟦xs⟧≡⟦ys⟧ = toℕ-injective-lemma x y (toℕ xs) (toℕ ys) condition eq
            xs≡ys : xs ≡ ys
            xs≡ys = toℕ-injective {isInj = InjCond⇒IsInj condition} xs ys (proj₂ x≡y×⟦xs⟧≡⟦ys⟧)
toℕ-injective {b} {d} {o}     {()} (x ∷ xs) (y ∷ ys) eq | NonInj reason

InjCond⇒Injective : ∀ {b} {d} {o} → InjCond b d o → Injective (Num⟶ℕ b d o)
InjCond⇒Injective condition {x} {y} = toℕ-injective {isInj = InjCond⇒IsInj condition} x y

NonInjCond⇏Injective : ∀ {b} {d} {o} → NonInjCond b d o → ¬ (Injective (Num⟶ℕ b d o))
-- NonInjCond⇏Injective (d>b: d>b) claim =
NonInjCond⇏Injective {_} {zero}  (d>b: ()) claim
NonInjCond⇏Injective {b} {suc d} {o} (d>b: d>b) claim =
    {!   !}
    where   ⟦11⟧≡⟦1+d⟧ : toℕ {b} (z ∷ z ∷ ∙) ≡ toℕ (Fin.fromℕ d ∷ ∙)
            ⟦11⟧≡⟦1+d⟧ =
                begin
                    o + zero + (o + zero + zero) * b
                ≡⟨ {!   !} ⟩
                    {!   !}
                ≡⟨ {!   !} ⟩
                    {!   !}
                ≡⟨ {!   !} ⟩
                    {!   !}
                ≡⟨ {!   !} ⟩
                    o + Fin.toℕ (Fin.fromℕ d) + zero
                ∎
NonInjCond⇏Injective (o≡0: o≡0) x = {!   !}

Injective? : ∀ b d o → Dec (Injective (Num⟶ℕ b d o))
Injective? b d o with injectionView b d o
Injective? b d o | Inj condition = yes (InjCond⇒Injective condition)
Injective? b d o | NonInj reason = no {!   !}



-- NonSurjCond⇏Surjective : ∀ {b} {d} {o} → NonSurjCond b d o → ¬ (Surjective (Num⟶ℕ b d o))
-- NonSurjCond⇏Surjective {_} {d} {o} Base≡0              claim =
--     lemma1 (from claim ⟨$⟩ suc o + d) (right-inverse-of claim (suc (o + d)))
-- NonSurjCond⇏Surjective NoDigits            claim =
--     lemma2      (from claim ⟨$⟩ 1)    (right-inverse-of claim 1)
-- NonSurjCond⇏Surjective (Offset≥2 p)        claim =
--     lemma3 p    (from claim ⟨$⟩ 1)    (right-inverse-of claim 1)
-- NonSurjCond⇏Surjective UnaryWithOnlyZeros     claim =
--     lemma4     (from claim ⟨$⟩ 1)     (right-inverse-of claim 1)
-- NonSurjCond⇏Surjective {_} {d} {o} (NotEnoughDigits p q) claim =
--     lemma5 p q (from claim ⟨$⟩ o + d) (right-inverse-of claim (o + d))



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
