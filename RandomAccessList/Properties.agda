module RandomAccessList.Properties where

open import BuildingBlock
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
import      BuildingBlock.BinaryLeafTree as BLT

open import RandomAccessList
open import RandomAccessList.Core
open import RandomAccessList.Core.Properties

open import Data.Nat
open import Data.Nat.Etc
open import Data.Nat.Properties.Simple
open import Data.Product as Prod
open import Data.Product hiding (map)
open import Data.Empty using (⊥-elim)
open import Function
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; True; fromWitnessFalse)
open import Relation.Nullary.Negation using (contraposition)

open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning

tailₙ-suc : ∀ {n A} → (xs : RandomAccessList A n) → (p : ⟦ xs ⟧ ≢ 0)
           → suc ⟦ tailₙ xs p ⟧ₙ ≡ ⟦ xs ⟧ₙ
tailₙ-suc {n} {A} [] p = ⊥-elim (p (⟦[]⟧≡0 ([] {A} {n}) refl))
tailₙ-suc (  0∷ xs) p =
    begin
        2 + (2 * ⟦ tailₙ xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p) ⟧ₙ)
    ≡⟨ sym (+-*-suc 2 ⟦ tailₙ xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p) ⟧ₙ) ⟩
        2 * suc ⟦ tailₙ xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p) ⟧ₙ
    ≡⟨ cong (_*_ 2) (tailₙ-suc xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p)) ⟩
        2 * ⟦ xs ⟧ₙ
    ∎
tailₙ-suc (x 1∷ xs) p = refl

tail-suc : ∀ {A} → (xs : RandomAccessList A 0) → (p : ⟦ xs ⟧ ≢ 0)
          → suc ⟦ tail xs p ⟧ ≡ ⟦ xs ⟧
tail-suc {A} [] p = ⊥-elim (p (⟦[]⟧≡0 ([] {A} {0}) refl))
tail-suc (0∷ xs) p =
    begin
        2 + (2 * ⟦ tailₙ xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p) ⟧ₙ + 0)
    ≡⟨ sym (+-assoc 2 (2 * ⟦ tailₙ xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p) ⟧ₙ) 0)  ⟩
        2 + 2 * ⟦ tailₙ xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p) ⟧ₙ + 0
    ≡⟨ cong (λ x → x + 0) (sym (+-*-suc 2 ⟦ tailₙ xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p) ⟧ₙ)) ⟩
        2 * suc ⟦ tailₙ xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p) ⟧ₙ + 0
    ≡⟨ cong (λ x → 2 * x + 0) (tailₙ-suc xs (⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p)) ⟩
        2 * ⟦ xs ⟧ₙ + 0
    ∎
tail-suc (x 1∷ xs) p = refl


headₙ-tailₙ-consₙ : ∀ {n A} → (xs : RandomAccessList A n) → (p : ⟦ xs ⟧ ≢ 0)
                 → consₙ (headₙ xs p) (tailₙ xs p) ≡ xs
headₙ-tailₙ-consₙ {n} {A} [] p = ⊥-elim (p (⟦[]⟧≡0 ([] {A} {n}) refl))
headₙ-tailₙ-consₙ (0∷ xs) p = let p' = contraposition (trans (⟦0∷xs⟧≡⟦xs⟧ xs)) p in
    begin
        consₙ (headₙ (0∷ xs) p) (tailₙ (0∷ xs) p)
    ≡⟨ refl ⟩
        consₙ (proj₁ (BLT.split (headₙ xs p'))) ((proj₂ (BLT.split (headₙ xs p'))) 1∷ tailₙ xs p')
    ≡⟨ refl ⟩
        0∷ (consₙ (Node ((proj₁ (BLT.split (headₙ xs p')))) ((proj₂ (BLT.split (headₙ xs p'))))) (tailₙ xs p'))
    ≡⟨ cong (λ x → 0∷ consₙ x (tailₙ xs p')) (BLT.split-merge (headₙ xs p')) ⟩
        0∷ consₙ (headₙ xs (p')) (tailₙ xs p')
    ≡⟨ cong 0∷_ (headₙ-tailₙ-consₙ xs p') ⟩
        0∷ xs
    ∎
headₙ-tailₙ-consₙ (x 1∷ xs) p = refl

head-tail-cons : ∀ {A} → (xs : RandomAccessList A 0) → (p : ⟦ xs ⟧ ≢ 0)
               → cons (head xs p) (tail xs p) ≡ xs
head-tail-cons {A} [] p = ⊥-elim (p (⟦[]⟧≡0 ([] {A} {0}) refl))
head-tail-cons (0∷ xs) p = let p' = contraposition (trans (⟦0∷xs⟧≡⟦xs⟧ xs)) p in
    begin
        cons (head (0∷ xs) p) (tail (0∷ xs) p)
    ≡⟨ cong (λ x → consₙ x (proj₂ (BLT.split (headₙ xs p')) 1∷ tailₙ xs p')) (lemma (proj₁ (BLT.split (headₙ xs p')))) ⟩
        0∷ consₙ (Node (proj₁ (BLT.split (headₙ xs p'))) (proj₂ (BLT.split (headₙ xs p')))) (tailₙ xs p')
    ≡⟨ cong (λ x → 0∷ consₙ x (tailₙ xs p')) (BLT.split-merge (headₙ xs p')) ⟩
        0∷ consₙ (headₙ xs p') (tailₙ xs p')
    ≡⟨ cong 0∷_ (headₙ-tailₙ-consₙ xs p') ⟩
        0∷ xs
    ∎
    where
        lemma : ∀ {A} → (xs : BinaryLeafTree A 0) → Leaf (BLT.head xs) ≡ xs
        lemma (Leaf x) = refl
head-tail-cons (Leaf x 1∷ xs) p = refl

{-
    begin
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ∎
-}
