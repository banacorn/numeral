module LinkedList where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat
import      Data.Fin as Fin
open import Data.Fin
  using (Fin)
  renaming (zero to Fzero; suc to Fsuc)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False)


data LinkedList (A : Set) : Set where
    [] : LinkedList A
    _∷_ : A → LinkedList A → LinkedList A

--------------------------------------------------------------------------------
-- to ℕ

⟦_⟧ : ∀ {A} → LinkedList A → ℕ
⟦     [] ⟧ = zero
⟦ x ∷ xs ⟧ = suc ⟦ xs ⟧

--------------------------------------------------------------------------------
-- predicates

null : ∀ {A} → LinkedList A → Set
null []      = ⊤
null (_ ∷ _) = ⊥

null? : ∀ {A} → (xs : LinkedList A) → Dec (null xs)
null? []       = yes tt
null? (x ∷ xs) = no (λ z → z)

--------------------------------------------------------------------------------
-- operations

incr : ∀ {A} → A → LinkedList A → LinkedList A
incr = _∷_

decr : ∀ {A} → (xs : LinkedList A) → False (null? xs) → LinkedList A
decr []       ()
decr (x ∷ xs) p = xs

_++_ : ∀ {A} → LinkedList A → LinkedList A → LinkedList A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

elemAt : ∀ {A} → (xs : LinkedList A) → Fin ⟦ xs ⟧ → A
elemAt []       ()
elemAt (x ∷ xs) Fzero    = x
elemAt (x ∷ xs) (Fsuc i) = elemAt xs i
