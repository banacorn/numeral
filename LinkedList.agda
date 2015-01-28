module LinkedList where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

data LinkedList (A : Set) : Set where
    [] : LinkedList A
    _∷_ : A → LinkedList A → LinkedList A


toℕ : {A : Set} → LinkedList A → ℕ
toℕ [] = zero
toℕ (x ∷ xs) = suc (toℕ xs)

-- predicates
Null : {A : Set} → LinkedList A → Set
Null [] = ⊤
Null (_ ∷ _) = ⊥

-- numerical-flavored operations
incr : {A : Set} → A → LinkedList A → LinkedList A
incr = _∷_

decr : {A : Set} → (xs : LinkedList A) → ¬ (Null xs) → LinkedList A
decr [] p with p tt
decr [] p | ()
decr (x ∷ xs) p = xs

add : {A : Set} → LinkedList A → LinkedList A → LinkedList A
add [] ys = ys
add (x ∷ xs) ys = x ∷ add xs ys

-- properties
incr-suc : {A : Set} → (x : A) → (xs : LinkedList A) → toℕ (incr x xs) ≡ suc (toℕ xs)
incr-suc a [] = refl
incr-suc a (x ∷ xs) = refl

Null-zero : {A : Set} → (xs : LinkedList A) → Null xs → toℕ xs ≡ zero
Null-zero [] p = refl
Null-zero (x ∷ xs) ()

decr-suc⁻¹ : {A : Set} → (xs : LinkedList A) → (p : ¬ (Null xs)) → toℕ xs ≡ suc (toℕ (decr xs p))
decr-suc⁻¹ [] p with p tt
decr-suc⁻¹ [] p | ()
decr-suc⁻¹ (x ∷ xs) p = refl

add-+ : {A : Set} → (xs : LinkedList A) → (ys : LinkedList A) → toℕ xs + toℕ ys ≡ toℕ (add xs ys)
add-+ [] ys = refl
add-+ (x ∷ xs) ys = cong suc (add-+ xs ys)
