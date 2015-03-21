module RandomAccessList.Standard.Numeral where

open import Data.List
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)
open PropEq.≡-Reasoning

data Digit : Set where
    zero : Digit
    one  : Digit

Binary : Set
Binary = List Digit

incr : Binary → Binary
incr []          = one  ∷ []
incr (zero ∷ xs) = one  ∷ xs
incr (one  ∷ xs) = zero ∷ incr xs

⟦_⟧ : Binary → ℕ
⟦ []        ⟧ = 0
⟦ zero ∷ xs ⟧ =     2 * ⟦ xs ⟧
⟦ one  ∷ xs ⟧ = 1 + 2 * ⟦ xs ⟧

*-0-absorb : (n m : ℕ) → n ≡ 0 → m * n ≡ 0
*-0-absorb n m p =
    begin
        m * n
    ≡⟨ cong (_*_ m) p ⟩
        m * 0
    ≡⟨ *-right-zero m ⟩
        0
    ∎

decr : (xs : Binary) → ⟦ xs ⟧ ≢ 0 → Binary
decr []          p = ⊥-elim (p refl)
decr (zero ∷ xs) p = one  ∷ decr xs (contraposition (*-0-absorb ⟦ xs ⟧ 2) p)
decr (one  ∷ xs) p = zero ∷ xs
