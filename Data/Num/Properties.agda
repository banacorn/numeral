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


WithZero≢Spurious : ∀ {b d} → b ≥ 1 → d ≥ 2 → d ≥ b → notSpurious b d 0
WithZero≢Spurious ()  d≥2      b≤d Base≡0
WithZero≢Spurious b≥1 ()       b≤d NoDigits
WithZero≢Spurious b≥1 d≥2      b≤d (Offset≥2 ())
WithZero≢Spurious b≥1 (s≤s ()) b≤d (UnaryWithOnly0s p)
WithZero≢Spurious b≥1 d≥2      b≤d (NotEnoughDigits p) = contradiction b≤d p

Zeroless≢Spurious : ∀ {b d} → b ≥ 1 → d ≥ 1 → d ≥ b → notSpurious b d 1
Zeroless≢Spurious ()  d≥1 b≤d Base≡0
Zeroless≢Spurious b≥1 ()  b≤d NoDigits
Zeroless≢Spurious b≥1 d≥1 b≤d (Offset≥2 (s≤s ()))
Zeroless≢Spurious b≥1 d≥1 b≤d (NotEnoughDigits p) = contradiction b≤d p

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
    → {✓ : notSpurious b d o}
    → (xs : Num b d o)
    → toℕ (1+ xs) ≡ suc (toℕ xs)
toℕ-1+ {b} {d} {o} xs   with surjectionView b d o
toℕ-1+ {b} {d}     ∙    | WithZero b≥1 d≥2 b≤d  =
    begin
        Fin.toℕ (fromℕ≤ d≥2) + b * zero
    ≡⟨ cong (λ x → Fin.toℕ (fromℕ≤ d≥2) + x) (*-right-zero b) ⟩
        Fin.toℕ (fromℕ≤ d≥2) + zero
    ≡⟨ +-right-identity (Fin.toℕ (fromℕ≤ d≥2)) ⟩
        Fin.toℕ (fromℕ≤ d≥2)
    ≡⟨ toℕ-fromℕ≤ d≥2 ⟩
        suc zero
    ∎
toℕ-1+ {b} {d} (x ∷ xs) | WithZero b≥1 d≥2 b≤d with full x
toℕ-1+ {b} {d} (x ∷ xs) | WithZero b≥1 d≥2 b≤d | yes p =
    begin
        Fin.toℕ {d} (digit+1-b x b≥1 p) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ (digit+1-b-lemma x b≥1 p)) ⟩    -- toℕ-fromℕ≤
        suc (Fin.toℕ x) ∸ b + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → suc (Fin.toℕ x) ∸ b + b * w) (toℕ-1+ {✓ = WithZero≢Spurious b≥1 d≥2 b≤d} xs) ⟩        -- induction
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
toℕ-1+ {b} {d} (x ∷ xs) | WithZero b≥1 d≥2 b≤d | no ¬p =
    cong (λ w → w + b * toℕ xs) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p))
toℕ-1+ {b} {d} ∙        | Zeroless b≥1 d≥1 b≤d =
    begin
        suc (Fin.toℕ (fromℕ≤ d≥1) + b * zero)
    ≡⟨ cong (λ x → suc (Fin.toℕ (fromℕ≤ d≥1)) + x) (*-right-zero b) ⟩
        suc (Fin.toℕ (fromℕ≤ d≥1) + zero)
    ≡⟨ cong (λ x → suc x + 0) (toℕ-fromℕ≤ d≥1) ⟩
        suc zero
    ∎
toℕ-1+ {b} {d} (x ∷ xs) | Zeroless b≥1 d≥1 b≤d with full x
toℕ-1+ {b} {d} (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | yes p =
    begin
        suc (Fin.toℕ (digit+1-b x b≥1 p)) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → suc w + b * toℕ (1+ xs)) (toℕ-fromℕ≤ (digit+1-b-lemma x b≥1 p)) ⟩    -- toℕ-fromℕ≤
        suc (suc (Fin.toℕ x) ∸ b) + b * toℕ (1+ xs)
    ≡⟨ cong (λ w → suc (suc (Fin.toℕ x) ∸ b) + b * w) (toℕ-1+ {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d} xs) ⟩      -- induction
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
toℕ-1+ {b} {d} (x ∷ xs) | Zeroless b≥1 d≥1 b≤d | no ¬p =
    cong (λ w → suc w + b * toℕ xs) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬p))
toℕ-1+ {✓ = claim} xs      | Spurious reason = contradiction refl (claim reason)


1+-fromℕ : ∀ {b d o}
    → {✓ : notSpurious b d o}
    → (n : ℕ)
    → 1+ (fromℕ {b} {d} {o} n) ≡ fromℕ (suc n)
1+-fromℕ {b} {d} {o} n with surjectionView b d o | inspect (surjectionView b d) o
1+-fromℕ             n | WithZero b≥1 d≥2 b≤d | [ eq ] rewrite eq = refl
1+-fromℕ             n | Zeroless b≥1 d≥1 b≤d | [ eq ] rewrite eq = refl
1+-fromℕ {✓ = claim} n | Spurious reason      | [ eq ] = contradiction refl (claim reason)

toℕ-fromℕ : ∀ {b d o}
    → {✓ : notSpurious b d o}
    → (n : ℕ)
    → toℕ (fromℕ {b} {d} {o} n) ≡ n
toℕ-fromℕ {b} {d} {o} n       with surjectionView b d o
toℕ-fromℕ {b} {d}     zero    | WithZero b≥1 d≥2 b≤d = refl
toℕ-fromℕ {b} {d}     (suc n) | WithZero b≥1 d≥2 b≤d =
    begin
        toℕ (1+ (fromℕ {b} {d} n))
    ≡⟨ toℕ-1+ {✓ = WithZero≢Spurious b≥1 d≥2 b≤d} (fromℕ {b} {d} n) ⟩
        suc (toℕ (fromℕ {b} {d} n))
    ≡⟨ cong suc (toℕ-fromℕ {b} {d} {✓ = WithZero≢Spurious b≥1 d≥2 b≤d} n) ⟩
        suc n
    ∎
toℕ-fromℕ {b} {d}     zero    | Zeroless b≥1 d≥1 b≤d = refl
toℕ-fromℕ {b} {d}     (suc n) | Zeroless b≥1 d≥1 b≤d =
    begin
        toℕ (1+ (fromℕ {b} {d} n))
    ≡⟨ toℕ-1+ {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d} (fromℕ {b} {d} n) ⟩
        suc (toℕ (fromℕ {b} {d} n))
    ≡⟨ cong suc (toℕ-fromℕ {b} {d} {✓ = Zeroless≢Spurious b≥1 d≥1 b≤d} n) ⟩
        suc n
    ∎
toℕ-fromℕ {✓ = claim}   n     | Spurious reason = contradiction refl (claim reason)

--
-- open import Function.Equality hiding (setoid; cong; _∘_; id)
-- open import Function.Surjection hiding (id; _∘_)
--
-- -- fromℕ that preserves equality
-- ℕ⟶Num : ∀ {b d o} → setoid ℕ ⟶ Num-Setoid b d o
-- ℕ⟶Num {b} {d} {o} = record
--     { _⟨$⟩_ = fromℕ
--     ; cong = cong (toℕ ∘ fromℕ {b} {d} {o})
--     }
--
-- -- toℕ that preserves equality
-- Num⟶ℕ : ∀ {b d o} → Num-Setoid b d o ⟶ setoid ℕ
-- Num⟶ℕ {b} {d} {o} = record { _⟨$⟩_ = toℕ ; cong = id }
--
-- Surjective? : ∀ {b d o}
--     → Dec (Surjective {From = Num-Setoid b d o} {To = setoid ℕ} Num⟶ℕ)
-- Surjective? {b} {d} {o} with surjectionView b d o | inspect (surjectionView b d) o
-- Surjective? {b} {d} | WithZero b≥1 d≥2 b≤d | [ eq ] = yes (record
--     { from = ℕ⟶Num
--     ; right-inverse-of = toℕ-fromℕ {b} {d} {✓ = fromWitness (WithZero≢Spurious eq)}
--     })
-- Surjective? {b} {d} | Zeroless b≥1 d≥1 b≤d | [ eq ] = yes (record
--     { from = ℕ⟶Num
--     ; right-inverse-of = toℕ-fromℕ {b} {d} {✓ = fromWitness (Zeroless≢Spurious eq)}
--     })
-- Surjective? {b} {d} {o} | Spurious | [ eq ] = no reason
--     where   reason : ¬ Surjective (Num⟶ℕ {b} {d} {o})
--             reason surj = {! Surjective.right-inverse-of surj 1  !}
--                 where   test : toℕ (Surjective.from surj ⟨$⟩ 1) ≡ 0
--                         test =
--                             begin
--                                 toℕ {b} {d} {o} (Surjective.from surj ⟨$⟩ 1)
--                             ≡⟨ refl ⟩
--                                 toℕ {b} {d} {o} {! fromℕ 1  !}
--                             ≡⟨ {!   !} ⟩
--                                 {!   !}
--                             ≡⟨ {!   !} ⟩
--                                 {!   !}
--                             ≡⟨ {!   !} ⟩
--                                 {!   !}
--                             ∎


-- ℕ⟶Num : ∀ {b d o}
--     → (view : SurjectionView b d o)
--     → {✓ : True (notSpurious? view)}
--     → setoid ℕ ⟶ Num-Setoid b d o
-- ℕ⟶Num (WithZero b≥1 d≥2 b≤d) = record
--     { _⟨$⟩_ = fromℕ
--     ; cong = cong (toℕ ∘ fromℕ) }
-- ℕ⟶Num (Zeroless b≥1 d≥1 b≤d) = record
--     { _⟨$⟩_ = fromℕ
--     ; cong = cong (toℕ ∘ fromℕ) }
-- ℕ⟶Num Spurious {()}
--
-- Num⟶ℕ : ∀ {b d o}
--     → (view : SurjectionView b d o)
--     → {✓ : True (notSpurious? view)}
--     → Num-Setoid b d o ⟶ setoid ℕ
-- Num⟶ℕ (WithZero b≥1 d≥2 b≤d) = record
--     { _⟨$⟩_ = toℕ
--     ; cong = id }
-- Num⟶ℕ (Zeroless b≥1 d≥1 b≤d) = record
--     { _⟨$⟩_ = toℕ
--     ; cong = id }
-- Num⟶ℕ Spurious {()}

-- Surjective? : ∀ {b d o}
--     → (view : SurjectionView b d o)
--     → {✓ : True (notSpurious? view)}
--     → Dec (Surjective {From = Num-Setoid b d o} {To = setoid ℕ} (Num⟶ℕ view {✓}))
-- Surjective? (WithZero b≥1 d≥2 b≤d) = yes (record
--     { from = ℕ⟶Num (WithZero b≥1 d≥2 b≤d)
--     ; right-inverse-of = toℕ-fromℕ (WithZero b≥1 d≥2 b≤d) })
-- Surjective? (Zeroless b≥1 d≥1 b≤d) = yes (record
--     { from = ℕ⟶Num (Zeroless b≥1 d≥1 b≤d)
--     ; right-inverse-of = toℕ-fromℕ (Zeroless b≥1 d≥1 b≤d) })
-- Surjective? Spurious {()}


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
