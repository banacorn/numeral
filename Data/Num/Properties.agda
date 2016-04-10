module Data.Num.Properties where

open import Data.Num

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin.Properties hiding (setoid)
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


toℕ-digit+1-b : ∀ {d b} (x : Digit d) → (b≥1 : b ≥ 1) → (p : suc (Fin.toℕ x) ≡ d)
    → Fin.toℕ (digit+1-b x b≥1 p) ≡ suc (Fin.toℕ x) ∸ b
toℕ-digit+1-b {d} {b} x b≥1 p = toℕ-fromℕ≤ $ start
        suc (suc (Fin.toℕ x) ∸ b)
    ≤⟨ s≤s (∸-mono ≤-refl b≥1) ⟩
        suc (Fin.toℕ x)
    ≤⟨ reflexive p ⟩
        d
    □


toℕ-1+ : ∀ {b d o}
    → (view : SurjectionView b d o)
    → {notSpurious : True (notSpurious? view)}
    → (xs : Num b d o)
    → toℕ (1+ view {notSpurious} xs) ≡ suc (toℕ xs)
toℕ-1+ (WithZero {b} b≥1 d≥2 b≤d) ∙ =
    begin
        Fin.toℕ (fromℕ≤ d≥2) + b * zero
    ≡⟨ cong (λ x → Fin.toℕ (fromℕ≤ d≥2) + x) (*-right-zero b) ⟩
        Fin.toℕ (fromℕ≤ d≥2) + zero
    ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ d≥2)) ⟩
        Fin.toℕ (fromℕ≤ d≥2)
    ≡⟨ toℕ-fromℕ≤ d≥2 ⟩
        suc zero
    ∎
toℕ-1+ (WithZero {b} {d} b≥1 d≥2 b≤d) (x ∷ xs) with full x
toℕ-1+ (WithZero {b} {d} b≥1 d≥2 b≤d) (x ∷ xs) | yes p =
    begin
        Fin.toℕ {d} (digit+1-b x b≥1 p) + b * toℕ (1+ (WithZero b≥1 d≥2 b≤d) xs)
    ≡⟨ cong (λ w → w + b * toℕ (1+ (WithZero b≥1 d≥2 b≤d) xs)) (toℕ-fromℕ≤ (digit+1-b-lemma x b≥1 p)) ⟩    -- toℕ-fromℕ≤
        suc (Fin.toℕ x) ∸ b + b * toℕ (1+ (WithZero b≥1 d≥2 b≤d) xs)
    ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ b + b * w) (toℕ-1+ (WithZero b≥1 d≥2 b≤d) xs) ⟩        -- induction
        suc (Fin.toℕ x) ∸ b + b * suc (toℕ xs)
    ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ b + w) (*-comm b (suc (toℕ xs))) ⟩
        suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b)
    ≡⟨ sym (+-assoc (suc (Fin.toℕ x) ∸ b) b (toℕ xs * b)) ⟩
        suc (Fin.toℕ x) ∸ b + b + toℕ xs * b
    ≡⟨ cong (λ w → w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
        b + (suc (Fin.toℕ x) ∸ b) + toℕ xs * b
    ≡⟨ cong (λ w → w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
            start
                b
            ≤⟨ b≤d ⟩
                d
            ≤⟨ reflexive (sym p) ⟩
                suc (Fin.toℕ x)
            □)) ⟩
        suc (Fin.toℕ x) + toℕ xs * b
    ≡⟨ cong (λ w → suc (Fin.toℕ x) + w) (*-comm (toℕ xs) b) ⟩
        suc (Fin.toℕ x + b * toℕ xs)
    ∎
toℕ-1+ (WithZero {b} b≥1 d≥2 b≤d) (x ∷ xs) | no ¬p =
    cong (λ w → w + b * toℕ xs) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p))
toℕ-1+ (Zeroless {b} b≥1 d≥1 b≤d) ∙ =
    begin
        suc (Fin.toℕ (fromℕ≤ d≥1) + b * zero)
    ≡⟨ cong (λ x → suc (Fin.toℕ (fromℕ≤ d≥1)) + x) (*-right-zero b) ⟩
        suc (Fin.toℕ (fromℕ≤ d≥1) + zero)
    ≡⟨ cong (λ x → suc x + 0) (toℕ-fromℕ≤ d≥1) ⟩
        suc zero
    ∎
toℕ-1+ (Zeroless {b} {d} b≥1 d≥1 b≤d) (x ∷ xs) with full x
toℕ-1+ (Zeroless {b} {d} b≥1 d≥1 b≤d) (x ∷ xs) | yes p =
    begin
        suc (Fin.toℕ (digit+1-b x b≥1 p)) + b * toℕ (1+ (Zeroless b≥1 d≥1 b≤d) xs)
    ≡⟨ cong (λ w → suc w + b * toℕ (1+ (Zeroless b≥1 d≥1 b≤d) xs)) (toℕ-fromℕ≤ (digit+1-b-lemma x b≥1 p)) ⟩    -- toℕ-fromℕ≤
        suc (suc (Fin.toℕ x) ∸ b) + b * toℕ (1+ (Zeroless b≥1 d≥1 b≤d) xs)
    ≡⟨ cong (λ w → suc (suc (Fin.toℕ x) ∸ b) + b * w) (toℕ-1+ (Zeroless b≥1 d≥1 b≤d) xs) ⟩      -- induction
        suc (suc (Fin.toℕ x) ∸ b + b * suc (toℕ xs))
    ≡⟨ cong (λ w → suc (suc (Fin.toℕ x) ∸ b + w)) (*-comm b (suc (toℕ xs))) ⟩
        suc (suc (Fin.toℕ x) ∸ b + (b + toℕ xs * b))
    ≡⟨  sym (+-assoc (suc (suc (Fin.toℕ x) ∸ b)) b (toℕ xs * b)) ⟩
        suc (suc (Fin.toℕ x) ∸ b + b + toℕ xs * b)
    ≡⟨ cong (λ w → suc w + toℕ xs * b) (+-comm (suc (Fin.toℕ x) ∸ b) b) ⟩
        suc (b + (suc (Fin.toℕ x) ∸ b)) + toℕ xs * b
    ≡⟨ cong (λ w → suc w + toℕ xs * b) (m+n∸m≡n (                                               -- m+n∸m≡n
            start
                b
            ≤⟨ b≤d ⟩
                d
            ≤⟨ reflexive (sym p) ⟩
                suc (Fin.toℕ x)
            □)) ⟩
        suc (suc (Fin.toℕ x + toℕ xs * b))
    ≡⟨ cong (λ w → suc (suc (Fin.toℕ x + w))) (*-comm (toℕ xs) b) ⟩
        suc (suc (Fin.toℕ x + b * toℕ xs))
    ∎
toℕ-1+ (Zeroless {b} {d} b≥1 d≥1 b≤d) (x ∷ xs) | no ¬p =
    cong (λ w → suc w + b * toℕ xs) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p))
toℕ-1+ Spurious       {()} xs -- die!!!!!

1+-fromℕ : ∀ {b d o}
    → (view : SurjectionView b d o)
    → {✓ : True (notSpurious? view)}
    → (n : ℕ)
    → 1+ view {✓} (fromℕ view {✓} n) ≡ fromℕ view {✓} (suc n)
1+-fromℕ (WithZero b≥1 d≥2 b≤d) n = refl
1+-fromℕ (Zeroless b≥1 d≥1 b≤d) n = refl
1+-fromℕ Spurious {()} n

toℕ-fromℕ : ∀ {b d o}
    → (view : SurjectionView b d o)
    → {✓ : True (notSpurious? view)}
    → (n : ℕ)
    → toℕ (fromℕ view {✓} n) ≡ n
toℕ-fromℕ (WithZero b≥1 d≥2 b≤d) zero = refl
toℕ-fromℕ (WithZero b≥1 d≥2 b≤d) (suc n) =
    begin
        toℕ (1+ (WithZero b≥1 d≥2 b≤d) (fromℕ (WithZero b≥1 d≥2 b≤d) n))
    ≡⟨ toℕ-1+ (WithZero b≥1 d≥2 b≤d) (fromℕ (WithZero b≥1 d≥2 b≤d) n) ⟩
        suc (toℕ (fromℕ (WithZero b≥1 d≥2 b≤d) n))
    ≡⟨ cong suc (toℕ-fromℕ (WithZero b≥1 d≥2 b≤d) n) ⟩
        suc n
    ∎
toℕ-fromℕ (Zeroless b≥1 d≥1 b≤d) zero = refl
toℕ-fromℕ (Zeroless b≥1 d≥1 b≤d) (suc n) =
    begin
        toℕ (1+ (Zeroless b≥1 d≥1 b≤d) (fromℕ (Zeroless b≥1 d≥1 b≤d) n))
    ≡⟨ toℕ-1+ (Zeroless b≥1 d≥1 b≤d) (fromℕ (Zeroless b≥1 d≥1 b≤d) n) ⟩
        suc (toℕ (fromℕ (Zeroless b≥1 d≥1 b≤d) n))
    ≡⟨ cong suc (toℕ-fromℕ (Zeroless b≥1 d≥1 b≤d) n) ⟩
        suc n
    ∎
toℕ-fromℕ Spurious {()} n

open import Function.Equality hiding (setoid; cong; _∘_; id)
open import Function.Surjection hiding (id; _∘_)

-- fromℕ that preserve equality
ℕ⟶Num : ∀ {b d o}
    → (view : SurjectionView b d o)
    → {✓ : True (notSpurious? view)}
    → setoid ℕ ⟶ Num-Setoid b d o
ℕ⟶Num (WithZero b≥1 d≥2 b≤d) = record
    { _⟨$⟩_ = fromℕ (WithZero b≥1 d≥2 b≤d)
    ; cong = cong (toℕ ∘ fromℕ (WithZero b≥1 d≥2 b≤d)) }
ℕ⟶Num (Zeroless b≥1 d≥1 b≤d) = record
    { _⟨$⟩_ = fromℕ (Zeroless b≥1 d≥1 b≤d)
    ; cong = cong (toℕ ∘ fromℕ (Zeroless b≥1 d≥1 b≤d)) }
ℕ⟶Num Spurious {()}

Num⟶ℕ : ∀ {b d o}
    → (view : SurjectionView b d o)
    → {✓ : True (notSpurious? view)}
    → Num-Setoid b d o ⟶ setoid ℕ
Num⟶ℕ (WithZero b≥1 d≥2 b≤d) = record
    { _⟨$⟩_ = toℕ
    ; cong = id }
Num⟶ℕ (Zeroless b≥1 d≥1 b≤d) = record
    { _⟨$⟩_ = toℕ
    ; cong = id }
Num⟶ℕ Spurious {()}

Surjective? : ∀ {b d o}
    → (view : SurjectionView b d o)
    → {✓ : True (notSpurious? view)}
    → Dec (Surjective {From = Num-Setoid b d o} {To = setoid ℕ} (Num⟶ℕ view {✓}))
Surjective? (WithZero b≥1 d≥2 b≤d) = yes (record
    { from = ℕ⟶Num (WithZero b≥1 d≥2 b≤d)
    ; right-inverse-of = toℕ-fromℕ (WithZero b≥1 d≥2 b≤d) })
Surjective? (Zeroless b≥1 d≥1 b≤d) = yes (record
    { from = ℕ⟶Num (Zeroless b≥1 d≥1 b≤d)
    ; right-inverse-of = toℕ-fromℕ (Zeroless b≥1 d≥1 b≤d) })
Surjective? Spurious {()}


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
