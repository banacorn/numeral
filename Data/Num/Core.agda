module Data.Num.Core where


open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Data.Fin.Properties as FinProps using (bounded; toℕ-fromℕ≤)

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Function.Equality using (_⟶_)

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)


------------------------------------------------------------------------
-- Predicates on the Indices
------------------------------------------------------------------------

--
--
--
--                  |   |
--                  |   |   Redundant
--                  |   |
--                  |  -|
--     b ≡ d        ∙
--              |-  |
--     Sparse   |   |
--              |   |
--              |   |


Redundant : ∀ b d → Set
Redundant b d = b < d

Redundant? : ∀ b d → Dec (Redundant b d)
Redundant? b d = suc b ≤? d

Sparse : ∀ b d → Set
Sparse b d = b > d

Sparse? : ∀ b d → Dec (Sparse b d)
Sparse? b d = suc d ≤? b

Redundant⇒¬Sparse : ∀ {b d} → Redundant b d → ¬ (Sparse b d)
Redundant⇒¬Sparse {b} {d} redundant claim = contradiction claim (>⇒≰ (≤-step redundant))

Sparse⇒¬Redundant : ∀ {b d } → Sparse b d → ¬ (Redundant b d)
Sparse⇒¬Redundant {b} {d} sparse claim = contradiction claim (>⇒≰ (≤-step sparse))


--------------------------------------------------------------------------------
-- Digits
--------------------------------------------------------------------------------

Digit : ℕ → Set
Digit = Fin

-- converting to and from ℕ
Digit-toℕ : ∀ {d} → Digit d → ℕ → ℕ
Digit-toℕ x o = Fin.toℕ x + o


Digit-fromℕ : ∀ {d} → (n o : ℕ) → d + o ≥ n → Digit (suc d)
Digit-fromℕ {d} n o upper-bound with n ∸ o ≤? d
Digit-fromℕ {d} n o upper-bound | yes p = fromℕ≤ (s≤s p)
Digit-fromℕ {d} n o upper-bound | no ¬p = contradiction p ¬p
    where   p : n ∸ o ≤ d
            p = start
                    n ∸ o
                ≤⟨ ∸-mono {n} {d + o} {o} {o} upper-bound ≤-refl ⟩
                    (d + o) ∸ o
                ≤⟨ reflexive (m+n∸n≡m d o) ⟩
                    d
                □

Digit-toℕ-fromℕ : ∀ {d o}
    → (n : ℕ)
    → (upper-bound : d + o ≥ n)
    → (lower-bound :     o ≤ n)
    → Digit-toℕ (Digit-fromℕ {d} n o upper-bound) o ≡ n
Digit-toℕ-fromℕ {d} {o} n ub lb with n ∸ o ≤? d
Digit-toℕ-fromℕ {d} {o} n ub lb | yes q =
    begin
        Fin.toℕ (fromℕ≤ (s≤s q)) + o
    ≡⟨ cong (λ x → x + o) (toℕ-fromℕ≤ (s≤s q)) ⟩
        n ∸ o + o
    ≡⟨ m∸n+n≡m lb ⟩
        n
    ∎
Digit-toℕ-fromℕ {d} {o} n ub lb | no ¬q = contradiction q ¬q
    where   q : n ∸ o ≤ d
            q = +n-mono-inverse o $
                start
                    n ∸ o + o
                ≤⟨ reflexive (m∸n+n≡m lb) ⟩
                    n
                ≤⟨ ub ⟩
                    d + o
                □
-- Digit-toℕ-fromℕ≤ : ∀ {d o n} → (p : n < d) → Digit-toℕ (fromℕ≤ p) o ≡ n + o
-- Digit-toℕ-fromℕ≤ {d} {o} {n} p =
--     begin
--         Fin.toℕ (fromℕ≤ p) + o
--     ≡⟨ cong (λ w → w + o) (toℕ-fromℕ≤ p) ⟩
--         n + o
--     ∎


--------------------------------------------------------------------------------
-- Properties of Digits
--------------------------------------------------------------------------------

Digit<d+o : ∀ {d} → (x : Digit d) → (o : ℕ) → Digit-toℕ x o < d + o
Digit<d+o {d} x o = +n-mono o (bounded x)

--------------------------------------------------------------------------------
-- Predicates on Digits
--------------------------------------------------------------------------------

-- A digit at its greatest
Greatest : ∀ {d} (x : Digit d) → Set
Greatest {d} x = suc (Fin.toℕ x) ≡ d

Greatest? : ∀ {d} (x : Digit d) → Dec (Greatest x)
Greatest? {d} x = suc (Fin.toℕ x) ≟ d

greatest-digit : ∀ d → Digit (suc d)
greatest-digit d = Fin.fromℕ d

toℕ-greatest : ∀ {d o}
    → (x : Digit (suc d))
    → Greatest x
    → Digit-toℕ x o ≡ d + o
toℕ-greatest {d} {o} x greatest = suc-injective $ cong (λ w → w + o) greatest

greatest-of-all : ∀ {d} (o : ℕ) → (x y : Digit d) → Greatest x → Digit-toℕ x o ≥ Digit-toℕ y o
greatest-of-all o z     z      refl = ≤-refl
greatest-of-all o z     (s ()) refl
greatest-of-all o (s x) z      greatest = +n-mono o {zero} {suc (Fin.toℕ x)} z≤n
greatest-of-all o (s x) (s y)  greatest = s≤s (greatest-of-all o x y (suc-injective greatest))

greatest-digit-is-the-Greatest : ∀ d → Greatest (greatest-digit d)
greatest-digit-is-the-Greatest d = cong suc (FinProps.to-from d)

-- A digit at its least
Least : ∀ {d} (x : Digit d) → Set
Least z     = ⊤
Least (s x) = ⊥

Least? : ∀ {d} (x : Digit d) → Dec (Least x)
Least? z     = yes tt
Least? (s x) = no (λ z₁ → z₁)

least-digit : ∀ {d} → Digit (suc d)
least-digit = z

--------------------------------------------------------------------------------
-- Functions on Digits
--------------------------------------------------------------------------------

-- +1
digit+1 : ∀ {d} → (x : Digit d) → (¬greatest : ¬ (Greatest x)) → Fin d
digit+1 x ¬greatest = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬greatest)

Digit-toℕ-digit+1 : ∀ {d o}
    → (x : Digit d)
    → (¬greatest : ¬ (Greatest x))
    → Digit-toℕ (digit+1 x ¬greatest) o ≡ suc (Digit-toℕ x o)
Digit-toℕ-digit+1 {d} {o} x ¬greatest = cong (λ w → w + o) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬greatest))

digit+1-n-lemma : ∀ {d}
    → (x : Digit d)
    → Greatest x
    → (n : ℕ)
    → n > 0
    → suc (Fin.toℕ x) ∸ n < d
digit+1-n-lemma {zero } () greatest n n>0
digit+1-n-lemma {suc d} x greatest n n>0 = s≤s $ start
        suc (Fin.toℕ x) ∸ n
    ≤⟨ ∸-mono {suc (Fin.toℕ x)} {suc d} {n} (bounded x) ≤-refl ⟩
        suc d ∸ n
    ≤⟨ ∸-mono ≤-refl n>0 ⟩
        suc d ∸ 1
    ≤⟨ ≤-refl ⟩
        d
    □


-- +1 and then -n, useful for handling carrying on increment
digit+1-n : ∀ {d}
    → (x : Digit d)
    → Greatest x
    → (n : ℕ)
    → n > 0
    → Digit d
digit+1-n x greatest n n>0 = fromℕ≤ (digit+1-n-lemma x greatest n n>0)

Digit-toℕ-digit+1-n : ∀ {d o}
    → (x : Digit d)
    → (greatest : Greatest x)
    → (n : ℕ)
    → (n>0 : n > 0)
    → n ≤ d
    → Digit-toℕ (digit+1-n x greatest n n>0) o ≡ suc (Digit-toℕ x o) ∸ n
Digit-toℕ-digit+1-n {zero}  {o} () greatest n n>0 n≤d
Digit-toℕ-digit+1-n {suc d} {o} x greatest n n>0  n≤d =
    begin
        Fin.toℕ (digit+1-n x greatest n n>0) + o
    ≡⟨ cong (λ w → w + o) (toℕ-fromℕ≤ (digit+1-n-lemma x greatest n n>0)) ⟩
        suc (Fin.toℕ x) ∸ n + o
    ≡⟨ +-comm (suc (Fin.toℕ x) ∸ n) o ⟩
        o + (suc (Fin.toℕ x) ∸ n)
    ≡⟨ sym (+-∸-assoc o {suc (Fin.toℕ x)} {n} $
        start
            n
        ≤⟨ n≤d ⟩
            suc d
        ≤⟨ reflexive (sym greatest) ⟩
            suc (Fin.toℕ x)
        □)
    ⟩
        (o + suc (Fin.toℕ x)) ∸ n
    ≡⟨ cong (λ w → w ∸ n) (+-comm o (suc (Fin.toℕ x))) ⟩
        suc (Fin.toℕ x) + o ∸ n
    ∎


------------------------------------------------------------------------
-- Numbers
------------------------------------------------------------------------

infixr 5 _∷_

data Num : ℕ → ℕ → ℕ → Set where
    ∙   : ∀ {b d o} → Num b d o
    _∷_ : ∀ {b d o} → Digit d → Num b d o → Num b d o


Null : ∀ {b d o} → Num b d o → Set
Null ∙        = ⊤
Null (x ∷ xs) = ⊥

Null? : ∀ {b d o} → (xs : Num b d o) → Dec (Null xs)
Null? ∙        = yes tt
Null? (x ∷ xs) = no (λ z₁ → z₁)

------------------------------------------------------------------------
-- Converting from Num to ℕ
------------------------------------------------------------------------

⟦_⟧_ : ∀ {b d o} → (xs : Num b d o) → ¬ (Null xs) → ℕ
⟦_⟧_ {b} {_} {o} ∙             ¬null = contradiction tt ¬null
⟦_⟧_ {b} {_} {o} (x ∷ ∙)       ¬null = Digit-toℕ x o
⟦_⟧_ {b} {_} {o} (x ∷ x' ∷ xs) ¬null = Digit-toℕ x o + ⟦ x' ∷ xs ⟧ ¬null * b

⟦_∷_⟧ : ∀ {b d o} → (x : Digit d) → (xs : Num b d o) → ℕ
⟦ x ∷ xs ⟧ = ⟦ (x ∷ xs) ⟧ id


expand : ∀ {b d o}
    → (x : Digit d) → (xs : Num b d o)
    → (xs! : ¬ (Null xs))
    → ⟦ x ∷ xs ⟧ ≡ Digit-toℕ x o + ⟦ xs ⟧ xs! * b
expand {b} {d} {o} x ∙         xs! = contradiction tt xs!
expand {b} {d} {o} x (x' ∷ xs) xs! = refl


n∷-mono-strict : ∀ {b d o}
    → (x : Fin d) (xs : Num (suc b) d o)
    → (y : Fin d) (ys : Num (suc b) d o)
    → (¬null-xs : ¬ (Null xs))
    → (¬null-ys : ¬ (Null ys))
    → Digit-toℕ x o ≡ Digit-toℕ y o
    → ⟦ xs ⟧ ¬null-xs < ⟦ ys ⟧ ¬null-ys
    → ⟦ x ∷ xs ⟧ < ⟦ y ∷ ys ⟧
n∷-mono-strict             x ∙         y ys        ¬null-xs ¬null-ys ⟦x⟧≡⟦y⟧ ⟦xs⟧<⟦ys⟧ = contradiction tt ¬null-xs
n∷-mono-strict             x (x' ∷ xs) y ∙         ¬null-xs ¬null-ys ⟦x⟧≡⟦y⟧ ⟦xs⟧<⟦ys⟧ = contradiction tt ¬null-ys
n∷-mono-strict {b} {d} {o} x (x' ∷ xs) y (y' ∷ ys) ¬null-xs ¬null-ys ⟦x⟧≡⟦y⟧ ⟦xs⟧<⟦ys⟧ =
    start
        suc ⟦ x ∷ (x' ∷  xs) ⟧
    ≈⟨ refl ⟩
        suc (Fin.toℕ x + o) + ⟦ x' ∷ xs ⟧ * suc b
    ≈⟨ sym (+-suc (Fin.toℕ x + o) (⟦ x' ∷ xs ⟧ * suc b)) ⟩
        Fin.toℕ x + o + suc (⟦ x' ∷ xs ⟧ * suc b)
    ≤⟨ n+-mono (Fin.toℕ x + o) (s≤s (m≤n+m (⟦ x' ∷ xs ⟧ * suc b) b)) ⟩
        Fin.toℕ x + o + (suc b + ⟦ x' ∷ xs ⟧ * suc b)
    ≤⟨ reflexive ⟦x⟧≡⟦y⟧ +-mono *n-mono (suc b) ⟦xs⟧<⟦ys⟧ ⟩
        Fin.toℕ y + o + ⟦ y' ∷ ys ⟧ * suc b
    ≈⟨ refl ⟩
        ⟦ y ∷ (y' ∷ ys) ⟧
    □

∷ns-mono-strict : ∀ {b d o}
    → (x : Fin d) (xs : Num b d o)
    → (y : Fin d) (ys : Num b d o)
    → (xs! : ¬ (Null xs))
    → (ys! : ¬ (Null ys))
    → ⟦ xs ⟧ xs! ≡ ⟦ ys ⟧ ys!
    → Digit-toℕ x o < Digit-toℕ y o
    → ⟦ x ∷ xs ⟧ < ⟦ y ∷ ys ⟧
∷ns-mono-strict {b} {d} {o} x xs y ys xs! ys! ⟦xs⟧≡⟦ys⟧ ⟦x⟧<⟦y⟧ =
    start
        suc ⟦ x ∷ xs ⟧
    ≈⟨ cong suc (expand x xs xs!) ⟩
        suc (Fin.toℕ x + o + (⟦ xs ⟧ xs!) * b)
    ≤⟨ ⟦x⟧<⟦y⟧ +-mono *n-mono b (reflexive ⟦xs⟧≡⟦ys⟧) ⟩
        Fin.toℕ y + o + (⟦ ys ⟧ ys!) * b
    ≈⟨ sym (expand y ys ys!) ⟩
        ⟦ y ∷ ys ⟧
    □

tail-mono-strict : ∀ {b d o}
    → (x : Fin d) (xs : Num b d o)
    → (y : Fin d) (ys : Num b d o)
    → (xs! : ¬ (Null xs))
    → (ys! : ¬ (Null ys))
    → Greatest x
    → ⟦ x ∷ xs ⟧ < ⟦ y ∷ ys ⟧
    → ⟦ xs ⟧ xs! < ⟦ ys ⟧ ys!
tail-mono-strict {b} {_} {o} x xs y ys xs! ys! greatest p
    = *n-mono-strict-inverse b ⟦∷xs⟧<⟦∷ys⟧
    where
        ⟦x⟧≥⟦y⟧ : Digit-toℕ x o ≥ Digit-toℕ y o
        ⟦x⟧≥⟦y⟧ = greatest-of-all o x y greatest
        expanded-p : Digit-toℕ x o + (⟦ xs ⟧ xs!) * b < Digit-toℕ y o + (⟦ ys ⟧ ys!) * b
        expanded-p =
            start
                suc (Fin.toℕ x + o + (⟦ xs ⟧ xs!) * b)
            ≈⟨ cong suc $ sym (expand x xs xs!) ⟩
                suc ⟦ x ∷ xs ⟧
            ≤⟨ p ⟩
                ⟦ y ∷ ys ⟧
            ≈⟨ expand y ys ys! ⟩
                Fin.toℕ y + o + (⟦ ys ⟧ ys!) * b
            □
        ⟦∷xs⟧<⟦∷ys⟧ : ⟦ xs ⟧ xs! * b < ⟦ ys ⟧ ys! * b
        ⟦∷xs⟧<⟦∷ys⟧ = +-mono-contra ⟦x⟧≥⟦y⟧ expanded-p



------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

-- _≲_ : ∀ {b d o} → Num b d o → Num b d o → Set
-- xs ≲ ys = toℕ xs ≤ toℕ ys
--
-- -- _≋_ : ∀ {b d o} → Num b d o → Num b d o → Set
-- -- xs ≋ ys = toℕ xs ≡ toℕ ys
--
-- -- toℕ that preserves equality
-- Num⟶ℕ : ∀ b d o → setoid (Num b d o) ⟶ setoid ℕ
-- Num⟶ℕ b d o = record { _⟨$⟩_ = toℕ ; cong = cong toℕ }

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

-- _≋_ : ∀ {b d o}
--     → (xs ys : Num b d o)
--     → Dec ?
-- _≋_ {b}     {d}     {o} ∙        ∙        = yes = ?
--
-- _≋_ {b}     {d}     {o} ∙        (y ∷ ys) with Digit-toℕ y o ≟ 0
-- _≋_ {zero}  {d}     {o} ∙        (y ∷ ys) | yes p = ?
-- _≋_ {suc b} {d}         ∙        (y ∷ ys) | yes p = ?
-- _≋_ {b}     {d}         ∙        (y ∷ ys) | no ¬p = ?
--
-- _≋_ {b}     {d}     {o} (x ∷ xs) ∙        with Digit-toℕ x o ≟ 0
-- _≋_ {zero}              (x ∷ xs) ∙        | yes p = ?
-- _≋_ {suc b}             (x ∷ xs) ∙        | yes p = ?
-- _≋_ {b}     {d}     {o} (x ∷ xs) ∙        | no ¬p = ?
-- -- things get trickier here, we cannot say two numbers are equal or not base on
-- -- their LSD, since the system may be redundant.
-- _≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) with Digit-toℕ x o ≟ Digit-toℕ y o
-- _≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) | yes p = xs ≋ ys
-- _≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) | no ¬p = ⊥


------------------------------------------------------------------------
-- Predicates on Num
------------------------------------------------------------------------

Maximum : ∀ {b d o} → (xs : Num b d o) → ¬ (Null xs) → Set
Maximum {b} {d} {o} xs xs! = ∀ (ys : Num b d o) (ys! : ¬ (Null ys)) → ⟦ xs ⟧ xs! ≥ ⟦ ys ⟧ ys!

-- a system is bounded if there exists the greatest number
Bounded : ∀ b d o → Set
Bounded b d o = Σ[ xs ∈ Num b d o ] Σ[ xs! ∈ ¬ (Null xs) ] Maximum xs xs!

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
