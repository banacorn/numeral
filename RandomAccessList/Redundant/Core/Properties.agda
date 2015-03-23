module RandomAccessList.Redundant.Core.Properties where

open import BuildingBlock
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
open import RandomAccessList.Redundant.Core

open import Data.Nat
open import Data.Nat.Etc
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------
-- On ⟦_⟧ and ⟦_⟧ₙ

-- identity
⟦[]⟧ₙ≡0 : ∀ {A n} → (xs : 0-2-RAL A n) → xs ≡ [] → ⟦ xs ⟧ₙ ≡ 0
⟦[]⟧ₙ≡0 []            p  = refl
⟦[]⟧ₙ≡0 (      0∷ xs) ()
⟦[]⟧ₙ≡0 (x     1∷ xs) ()
⟦[]⟧ₙ≡0 (x , y 2∷ xs) ()

⟦[]⟧≡0 : ∀ {n A} → (xs : 0-2-RAL A n) → xs ≡ [] → ⟦ xs ⟧ ≡ 0
⟦[]⟧≡0 {zero }    [] p  = refl
⟦[]⟧≡0 {suc n}    [] p  = *-right-zero (2 * 2 ^ n)
⟦[]⟧≡0 (      0∷ xs) ()
⟦[]⟧≡0 (x     1∷ xs) ()
⟦[]⟧≡0 (x , y 2∷ xs) ()

⟦0∷xs⟧≡⟦xs⟧ : ∀ {n A} → (xs : 0-2-RAL A (suc n)) → ⟦ 0∷ xs ⟧ ≡ ⟦ xs ⟧
⟦0∷xs⟧≡⟦xs⟧ {zero} xs = +-right-identity (2 * ⟦ xs ⟧ₙ)
⟦0∷xs⟧≡⟦xs⟧ {suc n} xs =
    begin
        2 * 2 ^ n * (2 * ⟦ xs ⟧ₙ)
    ≡⟨ sym (*-assoc (2 * 2 ^ n) 2 ⟦ xs ⟧ₙ) ⟩
        ((2 * 2 ^ n) * 2) * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ x → x * ⟦ xs ⟧ₙ) (*-comm (2 * 2 ^ n) 2) ⟩
        (2 * (2 * 2 ^ n)) * ⟦ xs ⟧ₙ
    ∎

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

{-
⟦[]⟧≡⟦[]⟧ : ∀ {n A} → ⟦ [] {A} {suc n} ⟧ ≡ ⟦ [] {A} {n} ⟧
⟦[]⟧≡⟦[]⟧ {n} =
    begin
        (2 * 2 ^ n) * 0
    ≡⟨ *-right-zero (2 * 2 ^ n) ⟩
        0
    ≡⟨ sym (*-right-zero (2 ^ n)) ⟩
        2 ^ n * 0
    ∎


⟦0∷xs⟧≡⟦xs⟧ {zero} xs = +-right-identity (2 * ⟦ xs ⟧ₙ)
⟦0∷xs⟧≡⟦xs⟧ {suc n} xs =
    begin
        2 * 2 ^ n * (2 * ⟦ xs ⟧ₙ)
    ≡⟨ sym (*-assoc (2 * 2 ^ n) 2 ⟦ xs ⟧ₙ) ⟩
        2 * 2 ^ n * 2 * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ x → x * ⟦ xs ⟧ₙ) (*-assoc 2 (2 ^ n) 2) ⟩
        2 * (2 ^ n * 2) * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ x → 2 * x * ⟦ xs ⟧ₙ) (*-comm (2 ^ n) 2) ⟩
        (2 * (2 * 2 ^ n)) * ⟦ xs ⟧ₙ
    ∎

⟦0∷xs⟧≢0⇒⟦xs⟧≢0  : ∀ {n A}
                → (xs : 0-1-RAL A (suc n))
                → ⟦ 0∷ xs ⟧ ≢ 0
                → ⟦ xs ⟧ ≢ 0
⟦0∷xs⟧≢0⇒⟦xs⟧≢0 xs p = contraposition (trans (⟦0∷xs⟧≡⟦xs⟧ xs)) p
-}
