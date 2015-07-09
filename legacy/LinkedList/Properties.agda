module LinkedList.Properties where

open import LinkedList

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning



incr-suc : ∀ {A x} → {xs : LinkedList A} → ⟦ incr x xs ⟧ ≡ suc ⟦ xs ⟧
incr-suc {_} {x} {xs} = refl

decr-pred : ∀ {A} → {xs : LinkedList A} → (p : False (null? xs)) → ⟦ decr xs p ⟧ ≡ pred ⟦ xs ⟧
decr-pred {xs = []    } ()
decr-pred {xs = x ∷ xs} p = refl

++-left-indentity : ∀ {A} → {xs : LinkedList A} → [] ++ xs ≡ xs
++-left-indentity {A} {xs} = refl

++-right-indentity : ∀ {A} → {xs : LinkedList A} → [] ++ xs ≡ xs
++-right-indentity {A} {xs} = refl

⟦xs++ys⟧≡⟦xs⟧+⟦ys⟧ : ∀ {A} → (xs : LinkedList A)
                         → (ys : LinkedList A)
                         → ⟦ xs ++ ys ⟧ ≡ ⟦ xs ⟧ + ⟦ ys ⟧
⟦xs++ys⟧≡⟦xs⟧+⟦ys⟧ []       ys = refl
⟦xs++ys⟧≡⟦xs⟧+⟦ys⟧ (x ∷ xs) ys = cong suc (⟦xs++ys⟧≡⟦xs⟧+⟦ys⟧ xs ys)
