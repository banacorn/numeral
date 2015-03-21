module RandomAccessList.Zeroless.Properties where

open import BuildingBlock
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf; split)
open import RandomAccessList.Zeroless.Core
open import RandomAccessList.Zeroless.Core.Properties
open import RandomAccessList.Zeroless

open import Data.Unit using (tt)
open import Data.Nat
open import Data.Nat.Etc
open import Data.Nat.Properties.Simple
open import Data.Product as Prod

open import Function
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; True; fromWitnessFalse; fromWitness)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning

tailₙ-suc : ∀ {n A} → (xs : 1-2-RAL A n) → (p : ⟦ xs ⟧ ≢ 0)
           → suc ⟦ tailₙ xs p ⟧ₙ ≡ ⟦ xs ⟧ₙ
tailₙ-suc {n} {A}    [] p = contradiction (⟦[]⟧≡0 ([] {A} {n}) refl) p
tailₙ-suc (x     1∷ xs) p with ⟦ xs ⟧ ≟ 0
tailₙ-suc {n} (x 1∷ xs) p | yes q =
    begin
        suc 0
    ≡⟨ cong suc (sym (*-right-zero 0)) ⟩
        suc (2 * 0)
    ≡⟨ cong (λ w → suc (2 * w)) (sym (no-zero-divisor (2 * 2 ^ n) ⟦ xs ⟧ₙ (m^n≢0 2 (suc n) (λ ())) q)) ⟩
        suc (2 * ⟦ xs ⟧ₙ)
    ∎
tailₙ-suc (x     1∷ xs) p | no ¬q =
    begin
        3 + 2 * ⟦ tailₙ xs ¬q ⟧ₙ
    ≡⟨ cong suc (sym (+-*-suc 2 ⟦ tailₙ xs ¬q ⟧ₙ)) ⟩
        1 + 2 * suc ⟦ tailₙ xs ¬q ⟧ₙ
    ≡⟨ cong (λ w → 1 + 2 * w) (tailₙ-suc xs ¬q) ⟩
        1 + (2 * ⟦ xs ⟧ₙ)
    ∎
tailₙ-suc (x , y 2∷ xs) p = refl

tail-suc : ∀ {A} → (xs : 1-2-RAL A 0) → (p : ⟦ xs ⟧ ≢ 0)
         → suc ⟦ tail xs p ⟧ ≡ ⟦ xs ⟧
tail-suc {A}        [] p = contradiction (⟦[]⟧≡0 ([] {A} {0}) refl) p
tail-suc (x     1∷ xs) p with ⟦ xs ⟧ ≟ 0
tail-suc (x     1∷ xs) p | yes q = cong (λ w → suc (w + 0)) (sym q)
tail-suc (x     1∷ xs) p | no ¬q =
    begin
        3 + 2 * ⟦ tailₙ xs ¬q ⟧ₙ + 0
    ≡⟨ cong (λ w → 1 + w + 0) (sym (+-*-suc 2 ⟦ tailₙ xs ¬q ⟧ₙ)) ⟩
        1 + 2 * suc ⟦ tailₙ xs ¬q ⟧ₙ + 0
    ≡⟨ cong (λ w → 1 + 2 * w + 0) (tailₙ-suc xs ¬q) ⟩
        1 + 2 * ⟦ xs ⟧ₙ + 0
    ∎
tail-suc (x , y 2∷ xs) p = refl
