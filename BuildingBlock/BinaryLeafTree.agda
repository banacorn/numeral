module BuildingBlock.BinaryLeafTree where

open import Function
open import Data.Nat
open import Data.Nat.Exp
open import Data.Nat.Properties.Simple using (+-right-identity)
open import Data.Product using (_×_; _,_)
open import Data.Fin
    using (Fin; toℕ; fromℕ; fromℕ≤; reduce≥)
    renaming (zero to Fzero; suc to Fsuc)

open import Data.Empty

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)
open PropEq.≡-Reasoning
--------------------------------------------------------------------------------
-- Complete Binary Leaf Trees

data BinaryLeafTree (A : Set) : ℕ → Set where
    Leaf : A → BinaryLeafTree A 0
    Node : ∀ {n} → BinaryLeafTree A n
                 → BinaryLeafTree A n
                 → BinaryLeafTree A (suc n)

-- merge 2 BinaryLeafTree
split : ∀ {A n} → BinaryLeafTree A (suc n)
                → BinaryLeafTree A n × BinaryLeafTree A n
split (Node xs ys) = xs , ys

-- splits a BinaryLeafTree into 2
merge : ∀ {A n} → BinaryLeafTree A n
                → BinaryLeafTree A n
                → BinaryLeafTree A (suc n)
merge = Node

-- searching
transportFin : ∀ {a b} → a ≡ b → Fin a → Fin b
transportFin refl i = i

¬a≤b⇒b<a : ∀ {a b} → ¬ (a ≤ b) → b < a
¬a≤b⇒b<a {zero } {b    } p = ⊥-elim (p z≤n)
¬a≤b⇒b<a {suc a} {zero } p = s≤s z≤n
¬a≤b⇒b<a {suc a} {suc b} p = s≤s (¬a≤b⇒b<a (λ z → p (s≤s z)))

elemAt : ∀ {A n} → BinaryLeafTree A n → Fin (2 ^ n) → A
elemAt {n = zero}  (Leaf x)     Fzero = x
elemAt {n = zero}  (Leaf x)     (Fsuc ())
elemAt {n = suc n} (Node xs ys) i with (2 ^ n) ≤? toℕ i
elemAt {n = suc n} (Node xs ys) i | yes p = elemAt ys (transportFin (+-right-identity (2 ^ n)) (reduce≥ {2 ^ n} {2 ^ n + 0} i p))
elemAt {n = suc n} (Node xs ys) i | no ¬p = elemAt xs (fromℕ≤ (¬a≤b⇒b<a ¬p))

-- examples
private
    fier : BinaryLeafTree ℕ 2
    fier = Node
            (Node
                (Leaf 0)
                (Leaf 2))
            (Node
                (Leaf 3)
                (Leaf 1))
