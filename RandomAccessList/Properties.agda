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

open import Function
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; True; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning

tailₙ-suc : ∀ {n A} → (xs : RandomAccessList A n) → (p : False (null? xs))
           → suc ⟦ tailₙ xs p ⟧ₙ ≡ ⟦ xs ⟧ₙ
tailₙ-suc []        ()
tailₙ-suc (  0∷ xs) p  with null? xs
tailₙ-suc (  0∷ xs) () | yes q
tailₙ-suc (  0∷ xs) p  | no ¬q =
    begin
        2 + 2 * ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ
    ≡⟨ cong (λ x → 1 + x + 2 * ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ) (sym (+-right-identity 1)) ⟩
        2 * 1 + 2 * ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ
    ≡⟨ sym (distrib-left-*-+ 2 1 ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ) ⟩
        2 * suc ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ
    ≡⟨ cong (_*_ 2) (tailₙ-suc xs (fromWitnessFalse ¬q)) ⟩
        2 * ⟦ xs ⟧ₙ
    ∎
tailₙ-suc (x 1∷ xs) p = refl

tail-suc : ∀ {A} → (xs : RandomAccessList A 0) → (p : False (null? xs))
          → suc ⟦ tail xs p ⟧ ≡ ⟦ xs ⟧
tail-suc []        ()
tail-suc (  0∷ xs) p  with null? xs
tail-suc (  0∷ xs) () | yes q
tail-suc (  0∷ xs) p  | no ¬q =
    begin
        suc (suc (2 * ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ + 0))
    ≡⟨ cong (λ x → 1 + x + (2 * ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ + 0)) (sym (+-right-identity 1)) ⟩
        2 * 1 + (2 * ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ + 0)
    ≡⟨ +-assoc (2 * 1) (2 * ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ) 0 ⟩
        2 * 1 + 2 * ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ + 0
    ≡⟨ cong (λ x → x + 0) (sym (distrib-left-*-+ 2 1 ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ)) ⟩
        2 * suc ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ + 0
    ≡⟨ cong (λ x → 2 * x + 0) (tailₙ-suc xs (fromWitnessFalse ¬q)) ⟩
        ⟦ 0∷ xs ⟧
    ∎
tail-suc (x 1∷ xs) p  = refl



headₙ-tailₙ-consₙ : ∀ {n A} → (xs : RandomAccessList A n) → (p : False (null? xs))
                 → consₙ (headₙ xs p) (tailₙ xs p) ≡ xs
headₙ-tailₙ-consₙ []        ()
headₙ-tailₙ-consₙ (  0∷ xs) p  with null? xs
headₙ-tailₙ-consₙ (  0∷ xs) () | yes q
headₙ-tailₙ-consₙ (  0∷ xs) p  | no ¬q =
    begin
        consₙ (proj₁ (BLT.split (headₙ xs (fromWitnessFalse ¬q)))) (proj₂ (BLT.split (headₙ xs (fromWitnessFalse ¬q))) 1∷ tailₙ xs (fromWitnessFalse ¬q))
    ≡⟨ refl ⟩
        0∷ consₙ (Node (proj₁ (BLT.split (headₙ xs (fromWitnessFalse ¬q)))) (proj₂ (BLT.split (headₙ xs (fromWitnessFalse ¬q))))) (tailₙ xs (fromWitnessFalse ¬q))
    ≡⟨ cong (λ x → 0∷ consₙ x (tailₙ xs (fromWitnessFalse ¬q))) (BLT.split-merge (headₙ xs (fromWitnessFalse ¬q))) ⟩
        0∷ consₙ (headₙ xs (fromWitnessFalse ¬q)) (tailₙ xs (fromWitnessFalse ¬q))
    ≡⟨ cong 0∷_ (headₙ-tailₙ-consₙ xs (fromWitnessFalse ¬q)) ⟩
        0∷ xs
    ∎
headₙ-tailₙ-consₙ (x 1∷ xs) p  = refl

head-tail-cons : ∀ {A} → (xs : RandomAccessList A 0) → (p : False (null? xs))
               → cons (head xs p) (tail xs p) ≡ xs
head-tail-cons []      ()
head-tail-cons (0∷ xs) p  with null? xs
head-tail-cons (0∷ xs) () | yes q
head-tail-cons (0∷ xs) p  | no ¬q =
    begin
        cons (BLT.head (proj₁ (BLT.split (headₙ xs (fromWitnessFalse ¬q))))) (proj₂ (BLT.split (headₙ xs (fromWitnessFalse ¬q))) 1∷ tailₙ xs (fromWitnessFalse ¬q))
    ≡⟨ cong (λ x → consₙ x (proj₂ (BLT.split (headₙ xs (fromWitnessFalse ¬q))) 1∷ tailₙ xs (fromWitnessFalse ¬q))) (lemma (proj₁ (BLT.split (headₙ xs (fromWitnessFalse ¬q))))) ⟩
        0∷ consₙ (Node (proj₁ (BLT.split (headₙ xs (fromWitnessFalse ¬q))))  (proj₂ (BLT.split (headₙ xs (fromWitnessFalse ¬q))))) (tailₙ xs (fromWitnessFalse ¬q))
    ≡⟨ cong (λ x → 0∷ consₙ x (tailₙ xs (fromWitnessFalse ¬q))) (BLT.split-merge (headₙ xs (fromWitnessFalse ¬q))) ⟩
        0∷ consₙ (headₙ xs (fromWitnessFalse ¬q)) (tailₙ xs (fromWitnessFalse ¬q))
    ≡⟨ cong 0∷_ (headₙ-tailₙ-consₙ xs (fromWitnessFalse ¬q)) ⟩
        0∷ xs
    ∎
    where
        lemma : ∀ {A} → (xs : BinaryLeafTree A 0)
              → Leaf (BLT.head xs) ≡ xs
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
