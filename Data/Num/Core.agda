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

Digit-fromℕ-toℕ : ∀ {d o}
    → (n : ℕ)
    → (lower-bound :     o ≤ n)
    → (upper-bound : d + o ≥ n)
    → Digit-toℕ (Digit-fromℕ {d} n o upper-bound) o ≡ n
Digit-fromℕ-toℕ {d} {o} n lb ub with n ∸ o ≤? d
Digit-fromℕ-toℕ {d} {o} n lb ub | yes q =
    begin
        Fin.toℕ (fromℕ≤ (s≤s q)) + o
    ≡⟨ cong (λ x → x + o) (toℕ-fromℕ≤ (s≤s q)) ⟩
        n ∸ o + o
    ≡⟨ m∸n+n≡m lb ⟩
        n
    ∎
Digit-fromℕ-toℕ {d} {o} n lb ub | no ¬q = contradiction q ¬q
    where   q : n ∸ o ≤ d
            q = +n-mono-inverse o $
                start
                    n ∸ o + o
                ≤⟨ reflexive (m∸n+n≡m lb) ⟩
                    n
                ≤⟨ ub ⟩
                    d + o
                □

--------------------------------------------------------------------------------
-- Properties of all Digits
--------------------------------------------------------------------------------

Digit-upper-bound : ∀ {d} → (o : ℕ) → (x : Digit d) → Digit-toℕ x o < d + o
Digit-upper-bound {d} o x = +n-mono o (bounded x)

Digit-lower-bound : ∀ {d} → (o : ℕ) → (x : Digit d) → Digit-toℕ x o ≥ o
Digit-lower-bound {d} o x = m≤n+m o (Fin.toℕ x)

--------------------------------------------------------------------------------
-- Special Digits
--------------------------------------------------------------------------------

-- A digit at its greatest
Greatest : ∀ {d} (x : Digit d) → Set
Greatest {d} x = suc (Fin.toℕ x) ≡ d

Greatest? : ∀ {d} (x : Digit d) → Dec (Greatest x)
Greatest? {d} x = suc (Fin.toℕ x) ≟ d

greatest-digit : ∀ d → Digit (suc d)
greatest-digit d = Fin.fromℕ d

greatest-digit-toℕ : ∀ {d o}
    → (x : Digit (suc d))
    → Greatest x
    → Digit-toℕ x o ≡ d + o
greatest-digit-toℕ {d} {o} x greatest = suc-injective $ cong (λ w → w + o) greatest

greatest-of-all : ∀ {d} (o : ℕ) → (x y : Digit d) → Greatest x → Digit-toℕ x o ≥ Digit-toℕ y o
greatest-of-all o z     z      refl = ≤-refl
greatest-of-all o z     (s ()) refl
greatest-of-all o (s x) z      greatest = +n-mono o {zero} {suc (Fin.toℕ x)} z≤n
greatest-of-all o (s x) (s y)  greatest = s≤s (greatest-of-all o x y (suc-injective greatest))

greatest-digit-is-the-Greatest : ∀ d → Greatest (greatest-digit d)
greatest-digit-is-the-Greatest d = cong suc (FinProps.to-from d)

-- carry, 1 `max` o, in case that the least digit "o" is 0
carry : ℕ → ℕ
carry o = 1 ⊔ o

carry-lower-bound : ∀ {o} → carry o ≥ o
carry-lower-bound {o} = m≤n⊔m o 1

carry-upper-bound : ∀ {d o} → 2 ≤ suc d + o → carry o ≤ d + o
carry-upper-bound {d} {zero}  proper = ≤-pred proper
carry-upper-bound {d} {suc o} proper = m≤n+m (suc o) d

carry-digit : ∀ d o → 2 ≤ suc d + o → Digit (suc d)
carry-digit d o proper = Digit-fromℕ (carry o) o (carry-upper-bound {d} proper)

carry-digit-toℕ : ∀ d o
    → (proper : 2 ≤ suc (d + o))
    → Digit-toℕ (carry-digit d o proper) o ≡ carry o
carry-digit-toℕ d o proper = Digit-fromℕ-toℕ (carry o) (m≤n⊔m o 1) (carry-upper-bound {d} proper)


-- LCD-upper-bound-prim d zero    proper = ≤-pred proper
-- LCD-upper-bound-prim d (suc o) proper = m≤n+m (suc o) d
--
-- LCD : ∀ d o → 2 ≤ suc d + o → Digit (suc d)
-- LCD d o proper = Digit-fromℕ (1 ⊔ o) o (LCD-upper-bound-prim d o proper)
--
-- LCD-toℕ : ∀ d o
--     → (proper : 2 ≤ suc (d + o))
--     → Digit-toℕ (LCD d o proper) o ≡ 1 ⊔ o
-- LCD-toℕ d o proper = Digit-fromℕ-toℕ (1 ⊔ o) (m≤n⊔m o 1) (LCD-upper-bound-prim d o proper)
--
-- LCD-upper-bound : ∀ {d o}
--     → (proper : 2 ≤ suc (d + o))
--     → Digit-toℕ (LCD d o proper) o ≤ d + o
-- LCD-upper-bound {d} {o} proper =
--     start
--         Digit-toℕ (LCD d o proper) o
--     ≈⟨ LCD-toℕ d o proper ⟩
--         1 ⊔ o
--     ≤⟨ LCD-upper-bound-prim d o proper ⟩
--         d + o
--     □

--------------------------------------------------------------------------------
-- Functions on Digits
--------------------------------------------------------------------------------

-- +1
digit+1 : ∀ {d} → (x : Digit d) → (¬greatest : ¬ (Greatest x)) → Fin d
digit+1 x ¬greatest = fromℕ≤ {suc (Fin.toℕ x)} (≤∧≢⇒< (bounded x) ¬greatest)

digit+1-toℕ : ∀ {d o}
    → (x : Digit d)
    → (¬greatest : ¬ (Greatest x))
    → Digit-toℕ (digit+1 x ¬greatest) o ≡ suc (Digit-toℕ x o)
digit+1-toℕ {d} {o} x ¬greatest = cong (λ w → w + o) (toℕ-fromℕ≤ (≤∧≢⇒< (bounded x) ¬greatest))

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

digit+1-n-toℕ : ∀ {d o}
    → (x : Digit d)
    → (greatest : Greatest x)
    → (n : ℕ)
    → (n>0 : n > 0)
    → n ≤ d
    → Digit-toℕ (digit+1-n x greatest n n>0) o ≡ suc (Digit-toℕ x o) ∸ n
digit+1-n-toℕ {zero}  {o} () greatest n n>0 n≤d
digit+1-n-toℕ {suc d} {o} x greatest n n>0  n≤d =
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
    _∙  : ∀ {b d o} → Digit d → Num b d o
    _∷_ : ∀ {b d o} → Digit d → Num b d o → Num b d o

------------------------------------------------------------------------
-- Converting from Num to ℕ
------------------------------------------------------------------------

⟦_⟧ : ∀ {b d o} → (xs : Num b d o) → ℕ
⟦_⟧ {_} {_} {o} (x ∙)    = Digit-toℕ x o
⟦_⟧ {b} {_} {o} (x ∷ xs) = Digit-toℕ x o + ⟦ xs ⟧ * b

-- the least significant digit
lsd : ∀ {b d o} → (xs : Num b d o) → Digit d
lsd (x ∙   ) = x
lsd (x ∷ xs) = x

lsd-toℕ : ∀ {b d o} → (xs : Num b d o) → Digit-toℕ (lsd xs) o ≤ ⟦ xs ⟧
lsd-toℕ (x ∙) = ≤-refl
lsd-toℕ {b} {d} {o} (x ∷ xs) = m≤m+n (Digit-toℕ x o) (⟦ xs ⟧ * b)

------------------------------------------------------------------------
-- View of Num
------------------------------------------------------------------------

data NumView : ℕ → ℕ → ℕ → Set where
    NullBase    : ∀   d o                            → NumView 0       (suc d) o
    NoDigits    : ∀ b o                              → NumView b       0       o
    AllZeros    : ∀ b                                → NumView (suc b) 1       0
    Proper      : ∀ b d o → (proper : suc d + o ≥ 2) → NumView (suc b) (suc d) o

numView : ∀ b d o → NumView b d o
numView b       zero          o       = NoDigits b o
numView zero    (suc d)       o       = NullBase d o
numView (suc b) (suc zero)    zero    = AllZeros b
numView (suc b) (suc zero)    (suc o) = Proper b zero (suc o) (s≤s (s≤s z≤n))
numView (suc b) (suc (suc d)) o       = Proper b (suc d) o (s≤s (s≤s z≤n))

NoDigits-explode : ∀ {b o a} {Whatever : Set a}
    → (xs : Num b 0 o)
    → Whatever
NoDigits-explode (() ∙   )
NoDigits-explode (() ∷ xs)

------------------------------------------------------------------------
-- Properties of Num
------------------------------------------------------------------------

n∷-mono-strict : ∀ {b d o}
    → (x : Fin d) (xs : Num (suc b) d o)
    → (y : Fin d) (ys : Num (suc b) d o)
    → Digit-toℕ x o ≡ Digit-toℕ y o
    → ⟦ xs ⟧ < ⟦ ys ⟧
    → ⟦ x ∷ xs ⟧ < ⟦ y ∷ ys ⟧
n∷-mono-strict {b} {d} {o} x xs y ys ⟦x⟧≡⟦y⟧ ⟦xs⟧<⟦ys⟧ =
    start
        suc (Digit-toℕ x o) + ⟦ xs ⟧ * suc b
    ≈⟨ sym (+-suc (Digit-toℕ x o) (⟦ xs ⟧ * suc b)) ⟩
        Digit-toℕ x o + suc (⟦ xs ⟧ * suc b)
    ≤⟨ n+-mono (Digit-toℕ x o) (s≤s (m≤n+m (⟦ xs ⟧ * suc b) b)) ⟩
        Digit-toℕ x o + (suc ⟦ xs ⟧) * suc b
    ≤⟨ (reflexive ⟦x⟧≡⟦y⟧) +-mono (*n-mono (suc b) ⟦xs⟧<⟦ys⟧) ⟩
        Digit-toℕ y o + ⟦ ys ⟧ * suc b
    □


∷ns-mono-strict : ∀ {b d o}
    → (x : Fin d) (xs : Num b d o)
    → (y : Fin d) (ys : Num b d o)
    → ⟦ xs ⟧ ≡ ⟦ ys ⟧
    → Digit-toℕ x o < Digit-toℕ y o
    → ⟦ x ∷ xs ⟧ < ⟦ y ∷ ys ⟧
∷ns-mono-strict {b} {d} {o} x xs y ys ⟦xs⟧≡⟦ys⟧ ⟦x⟧<⟦y⟧ =
    start
        suc ⟦ x ∷ xs ⟧
    ≤⟨ ⟦x⟧<⟦y⟧ +-mono *n-mono b (reflexive ⟦xs⟧≡⟦ys⟧) ⟩
        ⟦ y ∷ ys ⟧
    □

tail-mono-strict : ∀ {b d o}
    → (x : Fin d) (xs : Num b d o)
    → (y : Fin d) (ys : Num b d o)
    → Greatest x
    → ⟦ x ∷ xs ⟧ < ⟦ y ∷ ys ⟧
    → ⟦ xs ⟧ < ⟦ ys ⟧
tail-mono-strict {b} {_} {o} x xs y ys greatest p
    = *n-mono-strict-inverse b ⟦∷xs⟧<⟦∷ys⟧
    where
        ⟦x⟧≥⟦y⟧ : Digit-toℕ x o ≥ Digit-toℕ y o
        ⟦x⟧≥⟦y⟧ = greatest-of-all o x y greatest
        ⟦∷xs⟧<⟦∷ys⟧ : ⟦ xs ⟧ * b < ⟦ ys ⟧ * b
        ⟦∷xs⟧<⟦∷ys⟧ = +-mono-contra ⟦x⟧≥⟦y⟧ p

tail-mono-strict-Null : ∀ {b d o}
    → (x : Fin d)
    → (y : Fin d) (ys : Num b d o)
    → Greatest x
    → ⟦ _∙ {b} {d} {o} x ⟧ < ⟦ y ∷ ys ⟧
    → 0 < ⟦ ys ⟧
tail-mono-strict-Null {b} {_} {o} x y ys greatest p
    = *n-mono-strict-inverse b ⟦∷∙⟧<⟦∷ys⟧
    where
        ⟦x⟧≥⟦y⟧ : Digit-toℕ x o ≥ Digit-toℕ y o
        ⟦x⟧≥⟦y⟧ = greatest-of-all o x y greatest
        ⟦∷∙⟧<⟦∷ys⟧ : 0 < ⟦ ys ⟧ * b
        ⟦∷∙⟧<⟦∷ys⟧ = +-mono-contra ⟦x⟧≥⟦y⟧ $
            start
                suc (Digit-toℕ x o) + 0
            ≈⟨ +-right-identity (suc (Digit-toℕ x o)) ⟩
                suc (Digit-toℕ x o)
            ≤⟨ p ⟩
                ⟦ y ∷ ys ⟧
            □
