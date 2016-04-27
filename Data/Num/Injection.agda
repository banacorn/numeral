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

data InjCond : ℕ → ℕ → ℕ → Set where
    Ordinary  : ∀ {b d o} → (b≥d : b ≥ d) → (o≥1 : o ≥ 1) → InjCond b d o
    Digitless : ∀ {b d o}                 → (d≡0 : d ≡ 0) → InjCond b 0 o -- having no digits at all

data NonInjCond : ℕ → ℕ → ℕ → Set where
    Redundant : ∀ {b d o}                  → (d>b : d > b) → NonInjCond b d o -- having to many digits
    WithZeros : ∀ {b d o} → (o≡0 : o ≡ 0) → (d≢0 : d ≢ 0) → NonInjCond b d 0 -- with leading zeroes

data InjectionView : ℕ → ℕ → ℕ → Set where
    Inj    : ∀ {b d o} → InjCond    b d o → InjectionView b d o
    NonInj : ∀ {b d o} → NonInjCond b d o → InjectionView b d o

injectionView : (b d o : ℕ) → InjectionView b d o
injectionView b zero    zero    = Inj    (Digitless refl)
injectionView b (suc d) zero    = NonInj (WithZeros refl (λ ()))
injectionView b d       (suc o) with d ≤? b
injectionView b d       (suc o) | yes p = Inj    (Ordinary p (s≤s z≤n))
injectionView b d       (suc o) | no ¬p = NonInj (Redundant (≰⇒> ¬p))


IsInjective : ℕ → ℕ → ℕ → Set
IsInjective b d o with injectionView b d o
IsInjective b d o | Inj    _ = ⊤
IsInjective b d o | NonInj _ = ⊥

InjCond⇒IsInj : ∀ {b d o} → InjCond b d o → IsInjective b d o
InjCond⇒IsInj {b} {d} {o} cond with injectionView b d o
InjCond⇒IsInj _                  | Inj _ = tt
InjCond⇒IsInj (Ordinary b≥d o≥1) | NonInj (Redundant d>b) = contradiction b≥d (>⇒≰ d>b)
InjCond⇒IsInj (Ordinary b≥d ())  | NonInj (WithZeros o≡0 d≢0)
InjCond⇒IsInj (Digitless d≡0)    | NonInj (Redundant ())
InjCond⇒IsInj (Digitless d≡0)    | NonInj (WithZeros refl d≢0) = contradiction refl d≢0

-- InjCond⇒b≥1 : ∀ {b d o} → InjCond b (suc d) o → b ≥ 1
-- InjCond⇒b≥1 {zero}  (bijCond b≥d: o≥1:) = contradiction b≥d: (>⇒≰ (s≤s z≤n))
-- InjCond⇒b≥1 {suc b} (bijCond b≥d: o≥1:) = s≤s z≤n
--


NonInjCond⇏IsInj : ∀ {b d o} → NonInjCond b d o → ¬ IsInjective b d o
NonInjCond⇏IsInj {b} {d} {o} reason claim with injectionView b d o
NonInjCond⇏IsInj (Redundant d>b)     claim | Inj (Ordinary b≥d o≥1) = contradiction b≥d (>⇒≰ d>b)
NonInjCond⇏IsInj (Redundant ())      claim | Inj (Digitless d≡0)
NonInjCond⇏IsInj (WithZeros o≡0 d≢0) claim | Inj (Ordinary b≥d ())
NonInjCond⇏IsInj (WithZeros o≡0 d≢0) claim | Inj (Digitless d≡0) = contradiction refl d≢0
NonInjCond⇏IsInj reason              ()    | NonInj _

Digit-toℕ-injective : ∀ {d} o (x y : Fin d)
    → Digit-toℕ x o ≡ Digit-toℕ y o -- o + toℕ x ≡ o + toℕ y
    → x ≡ y
Digit-toℕ-injective {_} o x y eq =
    Fin→ℕ-injective         -- cancels `Fin.toℕ`
        $ cancel-+-left o    -- cancels `o +`
        $ eq


n∷-mono-strict : ∀ {b d o} (x y : Fin d) (xs ys : Num b d o)
    → InjCond b d o
    → toℕ xs < toℕ ys
    → toℕ (x ∷ xs) < toℕ (y ∷ ys)
n∷-mono-strict {b} {_} {o} () () xs ys (Digitless d≡0)    ⟦xs⟧<⟦ys⟧
n∷-mono-strict {b} {d} {o} x  y  xs ys (Ordinary b≥d o≥1) ⟦xs⟧<⟦ys⟧ =
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
            ≤⟨ b≥d ⟩
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

toℕ-injective-⟦x∷xs⟧>0-lemma : ∀ {b d o}
    → o ≥ 1
    → (x : Fin d)
    → (xs : Num b d o)
    → toℕ (x ∷ xs) > 0
toℕ-injective-⟦x∷xs⟧>0-lemma {b} {d} {o} o≥1 x xs =
    start
        suc zero
    ≤⟨ o≥1 ⟩
        o
    ≤⟨ m≤m+n o (Fin.toℕ x) ⟩
        o + Fin.toℕ x
    ≤⟨ m≤m+n (o + Fin.toℕ x) (toℕ xs * b) ⟩
        o + Fin.toℕ x + toℕ xs * b
    □

toℕ-injective : ∀ {b d o}
    → {isInj : IsInjective b d o}
    → (xs ys : Num b d o)
    → toℕ xs ≡ toℕ ys
    → xs ≡ ys
toℕ-injective {b} {d} {o} xs ys eq with injectionView b d o
toℕ-injective                 ∙        ∙        eq | Inj (Ordinary b≥d o≥1) = refl
toℕ-injective                 ∙        (y ∷ ys) eq | Inj (Ordinary b≥d o≥1) = contradiction eq (<⇒≢ (toℕ-injective-⟦x∷xs⟧>0-lemma o≥1 y ys))
toℕ-injective                 (x ∷ xs) ∙        eq | Inj (Ordinary b≥d o≥1) = contradiction eq (>⇒≢ (toℕ-injective-⟦x∷xs⟧>0-lemma o≥1 x xs))
toℕ-injective {b} {zero} {o} (() ∷ xs) (y ∷ ys) eq | Inj cond
toℕ-injective {b} {suc d} {o} (x ∷ xs) (y ∷ ys) eq | Inj cond with compare (toℕ xs) (toℕ ys)
toℕ-injective {b} {suc d} {o} (x ∷ xs) (y ∷ ys) eq | Inj cond | tri< ⟦xs⟧<⟦ys⟧ _ _ = contradiction eq (<⇒≢ (n∷-mono-strict x y xs ys cond ⟦xs⟧<⟦ys⟧))
toℕ-injective {b} {suc d} {o} (x ∷ xs) (y ∷ ys) eq | Inj cond | tri≈ _ ⟦xs⟧≡⟦ys⟧ _ with compare (Digit-toℕ x o) (Digit-toℕ y o)
toℕ-injective {b} {suc d} {o} (x ∷ xs) (y ∷ ys) eq | Inj cond | tri≈ _ ⟦xs⟧≡⟦ys⟧ _ | tri< ⟦x⟧<⟦y⟧ _ _ = contradiction eq (<⇒≢ (∷ns-mono-strict x y xs ys ⟦xs⟧≡⟦ys⟧ ⟦x⟧<⟦y⟧))
toℕ-injective {b} {suc d} {o} (x ∷ xs) (y ∷ ys) eq | Inj cond | tri≈ _ ⟦xs⟧≡⟦ys⟧ _ | tri≈ _ ⟦x⟧≡⟦y⟧ _ = cong₂ _∷_ (Digit-toℕ-injective o x y ⟦x⟧≡⟦y⟧) (toℕ-injective {isInj = InjCond⇒IsInj cond} xs ys ⟦xs⟧≡⟦ys⟧)
toℕ-injective {b} {suc d} {o} (x ∷ xs) (y ∷ ys) eq | Inj cond | tri≈ _ ⟦xs⟧≡⟦ys⟧ _ | tri> _ _ ⟦x⟧>⟦y⟧ = contradiction eq (>⇒≢ (∷ns-mono-strict y x ys xs (sym ⟦xs⟧≡⟦ys⟧) ⟦x⟧>⟦y⟧))
toℕ-injective {b} {suc d} {o} (x ∷ xs) (y ∷ ys) eq | Inj cond | tri> _ _ ⟦xs⟧>⟦ys⟧ = contradiction eq (>⇒≢ ((n∷-mono-strict y x ys xs cond ⟦xs⟧>⟦ys⟧)))
toℕ-injective                 ∙        ∙        eq | Inj (Digitless d≡0) = refl
toℕ-injective                 ∙       (() ∷ ys) eq | Inj (Digitless d≡0)
toℕ-injective                 (() ∷ xs) ys      eq | Inj (Digitless d≡0)
toℕ-injective {isInj = ()}    xs        ys      eq | NonInj reason

InjCond⇒Injective : ∀ {b} {d} {o} → InjCond b d o → Injective (Num⟶ℕ b d o)
InjCond⇒Injective condition {x} {y} = toℕ-injective {isInj = InjCond⇒IsInj condition} x y

NonInjCond⇏Injective : ∀ {b} {d} {o} → NonInjCond b d o → ¬ (Injective (Num⟶ℕ b d o))
NonInjCond⇏Injective {zero} {zero}      (Redundant ()) claim
NonInjCond⇏Injective {zero} {suc d} {o} (Redundant d>b) claim =
    contradiction
        (claim
            {z ∷ ∙}
            {z ∷ z ∷ ∙}
            ⟦1∷∙⟧≡⟦1∷1∷∙⟧)
        (λ ())
    where   ⟦1∷∙⟧≡⟦1∷1∷∙⟧ : toℕ {zero} {suc d} {o} (z ∷ ∙) ≡ toℕ {zero} {suc d} {o} (z ∷ z ∷ ∙)
            ⟦1∷∙⟧≡⟦1∷1∷∙⟧ = cong (λ w → o + 0 + w) (sym (*-right-zero (o + 0 + 0)))
NonInjCond⇏Injective {suc b} {zero} (Redundant ()) claim
NonInjCond⇏Injective {suc b} {suc zero} (Redundant (s≤s ())) claim
NonInjCond⇏Injective {suc b} {suc (suc d)} {o} (Redundant d>b) claim =
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
NonInjCond⇏Injective {b} {zero} {_} (WithZeros o≡0 d≢0) claim = contradiction refl d≢0
NonInjCond⇏Injective {b} {suc d} {_} (WithZeros o≡0 d≢0) claim =
    contradiction
        (claim
            {z ∷ ∙}
            {∙}
            ⟦0∷∙⟧≡⟦∙⟧)
        (λ ())
    where   ⟦0∷∙⟧≡⟦∙⟧ : toℕ {b} {suc d} {0} (z ∷ ∙) ≡ toℕ {b} {suc d} {0} ∙
            ⟦0∷∙⟧≡⟦∙⟧ = refl

Injective? : ∀ b d o → Dec (Injective (Num⟶ℕ b d o))
Injective? b d o with injectionView b d o
Injective? b d o | Inj condition = yes (InjCond⇒Injective condition)
Injective? b d o | NonInj reason = no (NonInjCond⇏Injective reason)

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
