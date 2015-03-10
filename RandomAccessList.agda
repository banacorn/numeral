module RandomAccessList where

open import RandomAccessList.Core
open import RandomAccessList.Core.Properties
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
import BuildingBlock.BinaryLeafTree as BLT

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; fromℕ≤; reduce≥; toℕ)
import      Data.Fin as Fin
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Nat.Etc
open import Data.Product as Prod
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------
-- Operations

consₙ : ∀ {n A} → BinaryLeafTree A n → RandomAccessList A n → RandomAccessList A n
consₙ a []        = a 1∷ []
consₙ a (  0∷ xs) = a 1∷ xs
consₙ a (x 1∷ xs) =   0∷ (consₙ (Node a x) xs)

cons : ∀ {A} → A → RandomAccessList A 0 → RandomAccessList A 0
cons a xs = consₙ (Leaf a) xs


headₙ :  ∀ {n A} → (xs : RandomAccessList A n) → ⟦ xs ⟧ ≢ 0 → BinaryLeafTree A n
headₙ {n} {A} [] p = ⊥-elim (p (⟦[]⟧≡0 ([] {A} {n}) refl))
headₙ (  0∷ xs)  p = proj₁ (BLT.split (headₙ xs (contraposition (trans (⟦0∷xs⟧≡⟦xs⟧ xs)) p)))
headₙ (x 1∷ xs)  p = x

head : ∀ {A} → (xs : RandomAccessList A 0) → ⟦ xs ⟧ ≢ 0 → A
head xs p = BLT.head (headₙ xs p)

tailₙ : ∀ {n A} → (xs : RandomAccessList A n) → ⟦ xs ⟧ ≢ 0 → RandomAccessList A n
tailₙ {n} {A} [] p = ⊥-elim (p (⟦[]⟧≡0 ([] {A} {n}) refl))
tailₙ (  0∷ xs)  p = proj₂ (BLT.split (headₙ xs (contraposition (trans (⟦0∷xs⟧≡⟦xs⟧ xs)) p))) 1∷ tailₙ xs (contraposition (trans (⟦0∷xs⟧≡⟦xs⟧ xs)) p)
tailₙ (x 1∷ xs)  p = 0∷ xs

tail : ∀ {A} → (xs : RandomAccessList A 0) → ⟦ xs ⟧ ≢ 0 → RandomAccessList A 0
tail = tailₙ

--------------------------------------------------------------------------------
-- Searching

transportFin : ∀ {a b} → a ≡ b → Fin a → Fin b
transportFin refl i = i

splitIndex : ∀ {n A} → (x : BinaryLeafTree A n) → (xs : RandomAccessList A (suc n)) → ⟦ x 1∷ xs ⟧ ≡ (2 ^ n) + ⟦ xs ⟧
splitIndex {n} x xs =
    begin
        2 ^ n * suc (2 * ⟦ xs ⟧ₙ)
    ≡⟨ +-*-suc (2 ^ n) (2 * ⟦ xs ⟧ₙ) ⟩
        2 ^ n + 2 ^ n * (2 * ⟦ xs ⟧ₙ)
    ≡⟨ cong (_+_ (2 ^ n)) (sym (*-assoc (2 ^ n) 2 ⟦ xs ⟧ₙ)) ⟩
        2 ^ n + 2 ^ n * 2 * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ w → 2 ^ n + w * ⟦ xs ⟧ₙ) (*-comm (2 ^ n) 2) ⟩
        2 ^ n + (2 * 2 ^ n) * ⟦ xs ⟧ₙ
    ∎

elemAt : ∀ {n A} → (xs : RandomAccessList A n) → Fin ⟦ xs ⟧ → A
elemAt {zero}  (     []) ()
elemAt {suc n} {A} ( []) i  = elemAt {n} ([] {n = n}) (transportFin (⟦[]⟧≡⟦[]⟧ {n} {A}) i)
elemAt         (  0∷ xs) i  with ⟦ 0∷ xs ⟧ | inspect ⟦_⟧ (0∷ xs)
elemAt         (  0∷ xs) () | zero  | _
elemAt {n}     (  0∷ xs) i  | suc z | PropEq.[ eq ] = elemAt xs (transportFin (trans (sym eq) (⟦0∷xs⟧≡⟦xs⟧ xs)) i)
elemAt {n}     (x 1∷ xs) i  with (2 ^ n) ≤? toℕ i
elemAt {n}     (x 1∷ xs) i  | yes p rewrite splitIndex x xs = elemAt xs (reduce≥ i p)
elemAt         (x 1∷ xs) i  | no ¬p = BLT.elemAt x (fromℕ≤ (BLT.¬a≤b⇒b<a ¬p))
