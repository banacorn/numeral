module ZerolessRAL.Properties where

open import BuildingBlock
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf; split)
open import ZerolessRAL.Core
open import ZerolessRAL

open import Data.Unit using (tt)
open import Data.Nat
open import Data.Nat.Etc
open import Data.Nat.Properties.Simple
open import Data.Product as Prod

open import Function
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; True; fromWitnessFalse; fromWitness)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning

nullₙ-0 : ∀ {n A} → (xs : 1-2-RAL A n) → (p : True (null? xs)) → ⟦ xs ⟧ₙ ≡ 0
nullₙ-0 [] p = refl
nullₙ-0 (x 1∷ xs) ()
nullₙ-0 (x , y 2∷ xs) ()

tailₙ-suc : ∀ {n A} → (xs : 1-2-RAL A n) → (p : False (null? xs))
           → suc ⟦ tailₙ xs p ⟧ₙ ≡ ⟦ xs ⟧ₙ
tailₙ-suc [] ()
tailₙ-suc (x 1∷ []             ) p = refl
tailₙ-suc (x 1∷ (Node x₁ x₂ 1∷ xs)) p =
    begin
        suc ⟦ tailₙ (x 1∷ (Node x₁ x₂ 1∷ xs)) p ⟧ₙ
    ≡⟨ cong suc (sym (+-*-suc 2 ⟦ tailₙ (Node x₁ x₂ 1∷ xs) tt ⟧ₙ)) ⟩
        suc (2 * suc ⟦ tailₙ (Node x₁ x₂ 1∷ xs) tt ⟧ₙ)
    ≡⟨ cong (λ w → suc (2 * w)) (tailₙ-suc (Node x₁ x₂ 1∷ xs) tt) ⟩
        ⟦ x 1∷ (Node x₁ x₂ 1∷ xs) ⟧ₙ
    ∎
tailₙ-suc (x 1∷ (Node x₁ x₂ , y 2∷ xs)) p = cong (_+_ 3) (sym (+-suc (2 * ⟦ xs ⟧ₙ) (suc (2 * ⟦ xs ⟧ₙ + zero))))
tailₙ-suc (x , y 2∷ xs) p = refl

tail-suc : ∀ {A} → (xs : 1-2-RAL A 0) → (p : False (null? xs))
         → suc ⟦ tail xs p ⟧ ≡ ⟦ xs ⟧
tail-suc [] ()
tail-suc (x 1∷ xs) p with null? xs
tail-suc (x 1∷ xs) p | yes q =
    begin
        1
    ≡⟨ cong (λ w → suc (w + 0)) (sym (*-right-zero 0)) ⟩
        suc (2 * 0 + 0)
    ≡⟨ cong (λ w → suc (2 * w + 0)) (sym (nullₙ-0 xs (fromWitness q))) ⟩
        suc (2 * ⟦ xs ⟧ₙ + 0)
    ∎
tail-suc (x 1∷ xs) p | no ¬q =
    begin
        suc (suc (suc (2 * ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ + 0)))
    ≡⟨ cong (λ w → suc (suc w + 0)) (sym (+-suc ⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ (⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ + 0))) ⟩
        suc (suc (⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ +  suc (⟦ tailₙ xs (fromWitnessFalse ¬q) ⟧ₙ + 0) + 0))
    ≡⟨ cong (λ w → suc (2 * w + 0)) (tailₙ-suc xs (fromWitnessFalse ¬q)) ⟩
        suc (2 * ⟦ xs ⟧ₙ + 0)
    ∎
tail-suc (x₀ , x₁ 2∷ xs) p = sym (+-assoc 1 (1 + 2 * ⟦ xs ⟧ₙ) 0)

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
