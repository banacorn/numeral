module Data.Num.Digit where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤; toℕ; zero; suc)
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
Digit-toℕ x o = toℕ x + o

Digit-fromℕ : ∀ {d} → (n o : ℕ) → d + o ≥ n → Digit (suc d)
Digit-fromℕ {d} n o upper-bound with n ∸ o ≤? d
Digit-fromℕ {d} n o upper-bound | yes p = fromℕ≤ (s≤s p)
Digit-fromℕ {d} n o upper-bound | no ¬p = contradiction p ¬p
    where   p : n ∸ o ≤ d
            p = start
                    n ∸ o
                ≤⟨ ∸n-mono o upper-bound ⟩
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
        toℕ (fromℕ≤ (s≤s q)) + o
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
Digit-lower-bound {d} o x = m≤n+m o (toℕ x)

--------------------------------------------------------------------------------
-- Special Digits
--------------------------------------------------------------------------------

-- A digit at its greatest
Greatest : ∀ {d} (x : Digit d) → Set
Greatest {d} x = suc (toℕ x) ≡ d

Greatest? : ∀ {d} (x : Digit d) → Dec (Greatest x)
Greatest? {d} x = suc (toℕ x) ≟ d

greatest-digit : ∀ d → Digit (suc d)
greatest-digit d = Fin.fromℕ d

greatest-digit-toℕ : ∀ {d o}
    → (x : Digit (suc d))
    → Greatest x
    → Digit-toℕ x o ≡ d + o
greatest-digit-toℕ {d} {o} x greatest = suc-injective $ cong (λ w → w + o) greatest

greatest-of-all : ∀ {d} (o : ℕ) → (x y : Digit d) → Greatest x → Digit-toℕ x o ≥ Digit-toℕ y o
greatest-of-all o zero    zero     refl = ≤-refl
greatest-of-all o zero    (suc ()) refl
greatest-of-all o (suc x) zero     greatest = +n-mono o {zero} {suc (toℕ x)} z≤n
greatest-of-all o (suc x) (suc y)  greatest = s≤s (greatest-of-all o x y (suc-injective greatest))

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
digit+1 x ¬greatest = fromℕ≤ {suc (toℕ x)} (≤∧≢⇒< (bounded x) ¬greatest)

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
    → suc (toℕ x) ∸ n < d
digit+1-n-lemma {zero } () greatest n n>0
digit+1-n-lemma {suc d} x greatest n n>0 = s≤s $ start
        suc (toℕ x) ∸ n
    ≤⟨ ∸n-mono n (bounded x) ⟩
        suc d ∸ n
    ≤⟨ n∸-mono (suc d) n>0 ⟩
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
        toℕ (digit+1-n x greatest n n>0) + o
    ≡⟨ cong (λ w → w + o) (toℕ-fromℕ≤ (digit+1-n-lemma x greatest n n>0)) ⟩
        suc (toℕ x) ∸ n + o
    ≡⟨ +-comm (suc (toℕ x) ∸ n) o ⟩
        o + (suc (toℕ x) ∸ n)
    ≡⟨ sym (+-∸-assoc o {suc (toℕ x)} {n} $
        start
            n
        ≤⟨ n≤d ⟩
            suc d
        ≤⟨ reflexive (sym greatest) ⟩
            suc (toℕ x)
        □)
    ⟩
        (o + suc (toℕ x)) ∸ n
    ≡⟨ cong (λ w → w ∸ n) (+-comm o (suc (toℕ x))) ⟩
        suc (toℕ x) + o ∸ n
    ∎
