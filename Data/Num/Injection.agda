module Data.Num.Injection where

open import Data.Num.Core

open import Data.Nat hiding (compare)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra

open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Data.Fin.Properties
    using (toℕ-fromℕ≤; to-from; bounded; inject≤-lemma)
    renaming (toℕ-injective to Fin→ℕ-injective; _≟_ to _Fin≟_)
open import Data.Fin.Properties.Extra
open import Data.Sum
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
open StrictTotalOrder strictTotalOrder using (compare)


record InjCond (b d o : ℕ) : Set where
    constructor bijCond
    field
        b≥d: : b ≥ d
        o≥1: : o ≥ 1
open InjCond public

data NonInjCond : ℕ → ℕ → ℕ → Set where
    d>b: : ∀ {b d o} → (d>b : d > b) → NonInjCond b d o  -- having to many digits
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
InjCond⇒IsInj cond                  | Inj _ = tt
InjCond⇒IsInj (bijCond b≥d: o≥1:) | NonInj (d>b: d>b) = contradiction b≥d: (>⇒≰ d>b)
InjCond⇒IsInj (bijCond b≥d: ())   | NonInj (o≡0: refl)

InjCond⇒b≥1 : ∀ {b d o} → InjCond b (suc d) o → b ≥ 1
InjCond⇒b≥1 {zero}  (bijCond b≥d: o≥1:) = contradiction b≥d: (>⇒≰ (s≤s z≤n))
InjCond⇒b≥1 {suc b} (bijCond b≥d: o≥1:) = s≤s z≤n

NonInjCond⇏IsInj : ∀ {b d o} → NonInjCond b d o → ¬ IsInjective b d o
NonInjCond⇏IsInj {b} {d} {o} reason claim with injectionView b d o
NonInjCond⇏IsInj (d>b: d>b)  claim | Inj (bijCond b≥d: o≥1:) = contradiction b≥d: (>⇒≰ d>b)
NonInjCond⇏IsInj (o≡0: refl) claim | Inj (bijCond b≥d: ())
NonInjCond⇏IsInj reason      ()    | NonInj _


Digit-toℕ-injective : ∀ {d} o (x y : Fin d)
    → Digit-toℕ x o ≡ Digit-toℕ y o
    → x ≡ y
Digit-toℕ-injective {_} o x y eq =
    Fin→ℕ-injective         -- cancels `Fin.toℕ`
        $ cancel-+-left o    -- cancels `o +`
        $ eq


n∷-mono-strict : ∀ {b d o} (x y : Fin d) (xs ys : Num b d o)
    → InjCond b d o
    → toℕ xs < toℕ ys
    → toℕ (x ∷ xs) < toℕ (y ∷ ys)
n∷-mono-strict {b} {d} {o} x y xs ys cond ⟦xs⟧<⟦ys⟧ =
    start
        suc (Digit-toℕ x o) + toℕ xs * b
    ≤⟨ +n-mono (toℕ xs * b) $
        start
            suc (Digit-toℕ x o)
        ≈⟨ sym (+-suc o (Fin.toℕ x)) ⟩
            -- push `o` to the left
            o + suc (Fin.toℕ x)
        ≤⟨ n+-mono o $
            start
                suc (Fin.toℕ x)
            ≤⟨ bounded x ⟩
                d
            ≤⟨ b≥d: cond ⟩
                b
            ≤⟨ n≤m+n (Fin.toℕ y) b ⟩
                Fin.toℕ y + b
        □ ⟩
            o + (Fin.toℕ y + b)
        ≈⟨ sym (+-assoc o (Fin.toℕ y) b) ⟩
            Digit-toℕ y o + b
    □ ⟩
        Digit-toℕ y o + b + toℕ xs * b
    ≈⟨ +-assoc (Digit-toℕ y o) b (toℕ xs * b) ⟩
        Digit-toℕ y o + (b + toℕ xs * b)
    ≤⟨ n+-mono (Digit-toℕ y o) (*n-mono b ⟦xs⟧<⟦ys⟧) ⟩  -- replace `xs` with `ys`
        Digit-toℕ y o + toℕ ys * b
    □

∷ns-mono-strict : ∀ {b d o} (x y : Fin d) (xs ys : Num b d o)
    → toℕ xs ≡ toℕ ys
    → Digit-toℕ x o < Digit-toℕ y o
    → toℕ (x ∷ xs) < toℕ (y ∷ ys)
∷ns-mono-strict {b} {d} {o} x y xs ys ⟦xs⟧≡⟦ys⟧ ⟦x⟧<⟦y⟧ = start
        suc (Digit-toℕ x o + toℕ xs * b)
    ≈⟨ cong (λ w → suc (Digit-toℕ x o + w * b)) ⟦xs⟧≡⟦ys⟧ ⟩
        suc (Digit-toℕ x o + toℕ ys * b)
    ≤⟨ +n-mono (toℕ ys * b) ⟦x⟧<⟦y⟧ ⟩
        Digit-toℕ y o + toℕ ys * b
    □

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
toℕ-injective {b} {d    } {o} (x  ∷ xs) (y ∷ ys) eq with injectionView b d o
toℕ-injective {_} {zero }     (() ∷ xs) (y ∷ ys) eq | Inj condition
toℕ-injective {_} {suc _} {_} (x  ∷ xs) (y ∷ ys) eq | Inj condition with compare (toℕ xs) (toℕ ys)
toℕ-injective {_} {suc _}     (x  ∷ xs) (y ∷ ys) eq | Inj condition | tri< ⟦xs⟧<⟦ys⟧ _ _ = contradiction eq (<⇒≢ (n∷-mono-strict x y xs ys condition ⟦xs⟧<⟦ys⟧))
toℕ-injective {_} {suc _} {o} (x  ∷ xs) (y ∷ ys) eq | Inj condition | tri≈ _ ⟦xs⟧≡⟦ys⟧ _ with compare (Digit-toℕ x o) (Digit-toℕ y o)
toℕ-injective {_} {suc _} {_} (x  ∷ xs) (y ∷ ys) eq | Inj condition | tri≈ _ ⟦xs⟧≡⟦ys⟧ _ | tri< ⟦x⟧<⟦y⟧ _ _ = contradiction eq (<⇒≢ (∷ns-mono-strict x y xs ys ⟦xs⟧≡⟦ys⟧ ⟦x⟧<⟦y⟧))
toℕ-injective {_} {suc _} {o} (x  ∷ xs) (y ∷ ys) eq | Inj condition | tri≈ _ ⟦xs⟧≡⟦ys⟧ _ | tri≈ _ ⟦x⟧≡⟦y⟧ _ = cong₂ _∷_ (Digit-toℕ-injective o x y ⟦x⟧≡⟦y⟧) (toℕ-injective {isInj = InjCond⇒IsInj condition} xs ys ⟦xs⟧≡⟦ys⟧)
toℕ-injective {_} {suc _} {_} (x  ∷ xs) (y ∷ ys) eq | Inj condition | tri≈ _ ⟦xs⟧≡⟦ys⟧ _ | tri> _ _ ⟦x⟧>⟦y⟧ = contradiction eq (>⇒≢ (∷ns-mono-strict y x ys xs (sym ⟦xs⟧≡⟦ys⟧) ⟦x⟧>⟦y⟧))
toℕ-injective {_} {suc _} {_} (x  ∷ xs) (y ∷ ys) eq | Inj condition | tri> _ _ ⟦xs⟧>⟦ys⟧ = contradiction eq (>⇒≢ ((n∷-mono-strict y x ys xs condition ⟦xs⟧>⟦ys⟧)))
toℕ-injective {isInj = ()}    (x ∷ xs) (y ∷ ys) eq | NonInj reason


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

InjCond⇒Injective : ∀ {b} {d} {o} → InjCond b d o → Injective (Num⟶ℕ b d o)
InjCond⇒Injective condition {x} {y} = toℕ-injective {isInj = InjCond⇒IsInj condition} x y

NonInjCond⇏Injective : ∀ {b} {d} {o} → NonInjCond b d o → ¬ (Injective (Num⟶ℕ b d o))
NonInjCond⇏Injective {_} {zero}  (d>b: ()) claim
NonInjCond⇏Injective {zero} {suc d} {o} (d>b: d>b) claim =
    contradiction
        (claim
            {z ∷ ∙}
            {z ∷ z ∷ ∙}
            ⟦1∷∙⟧≡⟦1∷1∷∙⟧)
        (λ ())
    where   ⟦1∷∙⟧≡⟦1∷1∷∙⟧ : toℕ {zero} {suc d} {o} (z ∷ ∙) ≡ toℕ {zero} {suc d} {o} (z ∷ z ∷ ∙)
            ⟦1∷∙⟧≡⟦1∷1∷∙⟧ = cong (λ w → o + 0 + w) (sym (*-right-zero (o + 0 + 0)))
NonInjCond⇏Injective {suc b} {suc zero} (d>b: (s≤s ())) claim
NonInjCond⇏Injective {suc b} {suc (suc d)} {o} (d>b: d>b) claim =
    contradiction
        (claim
            {z ∷ s z ∷ ∙}
            {fromℕ≤ d>b ∷ z ∷ ∙}
            ⟦1∷2⟧≡⟦b+1∷1⟧)
        (λ ())
    where   ⟦1∷2⟧≡⟦b+1∷1⟧ : toℕ {suc b} {suc (suc d)} {o} (z ∷ s z ∷ ∙) ≡ toℕ {suc b} {suc (suc d)} {o} (fromℕ≤ {suc b} d>b ∷ z ∷ ∙)
            ⟦1∷2⟧≡⟦b+1∷1⟧ =
                begin
                    o + zero + (o + suc zero + zero) * suc b
                ≡⟨ cong (λ x → x + (o + suc zero + zero) * suc b) (+-right-identity o) ⟩
                    o + (o + suc zero + zero) * suc b
                ≡⟨ cong (λ x → o + (x + zero) * suc b) (+-suc o zero) ⟩
                    o + (suc (o + zero) + zero) * suc b
                ≡⟨ refl ⟩
                    o + (suc b + (o + zero + zero) * suc b)
                ≡⟨ sym (+-assoc o (suc b) ((o + zero + zero) * suc b)) ⟩
                    o + suc b + (o + zero + zero) * suc b
                ≡⟨ cong (λ x → o + x + (o + zero + zero) * suc b) (sym (toℕ-fromℕ≤ d>b)) ⟩
                    o + Fin.toℕ (fromℕ≤ d>b) + (o + zero + zero) * suc b
                ∎
NonInjCond⇏Injective {d = zero} (o≡0: o≡0) x = {!   !}
NonInjCond⇏Injective {d = suc d} (o≡0: o≡0) x = {!   !}
    -- {!   !}
    -- where   ⟦0∷∙⟧≡⟦∙⟧ : toℕ {b} {d} (z ∷ ∙) ≡ ?
    --         ⟦0∷∙⟧≡⟦∙⟧ = ?
--
-- Injective? : ∀ b d o → Dec (Injective (Num⟶ℕ b d o))
-- Injective? b d o with injectionView b d o
-- Injective? b d o | Inj condition = yes (InjCond⇒Injective condition)
-- Injective? b d o | NonInj reason = no {!   !}



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
