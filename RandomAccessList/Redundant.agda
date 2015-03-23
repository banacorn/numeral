module RandomAccessList.Redundant where

open import RandomAccessList.Redundant.Core
open import RandomAccessList.Redundant.Core.Properties
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
import BuildingBlock.BinaryLeafTree as BLT


open import Data.Product
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)

--------------------------------------------------------------------------------
--  Operations
--------------------------------------------------------------------------------

consₙ : ∀ {n A} → BinaryLeafTree A n → 0-2-RAL A n → 0-2-RAL A n
consₙ a []            = a 1∷ []
consₙ a (      0∷ xs) = a 1∷ xs
consₙ a (x     1∷ xs) = a , x 2∷ xs
consₙ a (x , y 2∷ xs) = a 1∷ consₙ (Node x y) xs

cons : ∀ {A} → A → 0-2-RAL A 0 → 0-2-RAL A 0
cons a xs = consₙ (Leaf a) xs

headₙ :  ∀ {n A} → (xs : 0-2-RAL A n) → ⟦ xs ⟧ ≢ 0 → BinaryLeafTree A n
headₙ {n} {A} []    p = contradiction (⟦[]⟧≡0 ([] {A} {n}) refl) p
headₙ (      0∷ xs) p = proj₁ (BLT.split (headₙ xs (contraposition (trans (⟦0∷xs⟧≡⟦xs⟧ xs))  p )))
headₙ (x     1∷ xs) p = x
headₙ (x , y 2∷ xs) p = x

head : ∀ {A} → (xs : 0-2-RAL A 0) → ⟦ xs ⟧ ≢ 0 → A
head xs p = BLT.head (headₙ xs p)


tailₙ : ∀ {n A} → (xs : 0-2-RAL A n) → ⟦ xs ⟧ ≢ 0 → 0-2-RAL A n
tailₙ {n} {A} []    p = contradiction (⟦[]⟧≡0 ([] {A} {n}) refl) p
tailₙ (      0∷ xs) p = proj₂ (BLT.split (headₙ xs (contraposition (trans (⟦0∷xs⟧≡⟦xs⟧ xs)) p))) 1∷ tailₙ xs (contraposition (trans (⟦0∷xs⟧≡⟦xs⟧ xs)) p)
tailₙ (x     1∷ xs) p = 0∷ xs
tailₙ (x , y 2∷ xs) p = y 1∷ xs

tail : ∀ {A} → (xs : 0-2-RAL A 0) → ⟦ xs ⟧ ≢ 0 → 0-2-RAL A 0
tail = tailₙ
