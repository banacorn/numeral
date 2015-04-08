module RandomAccessList.Redundant.Core.Properties where

open import BuildingBlock
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
open import RandomAccessList.Redundant.Core

open import Data.Num.Redundant
open import Data.Num.Redundant.Properties

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Etc
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning

⟦[]⟧≈zero∷[] : ∀ {n A} → (xs : 0-2-RAL A n) → {xs≣[] : xs ≡ []} → ⟦ xs ⟧ ≈ zero ∷ []
⟦[]⟧≈zero∷[] {n} {A} [] {xs≡[]} = <<<-zero n (zero ∷ []) {eq refl}
⟦[]⟧≈zero∷[] (      0∷ xs) {()}
⟦[]⟧≈zero∷[] (x     1∷ xs) {()}
⟦[]⟧≈zero∷[] (x , y 2∷ xs) {()}

--------------------------------------------------------------------------------
-- On ⟦_⟧ and ⟦_⟧ₙ

{-
⟦[]⟧ₙ≡0 : ∀ {A n} → (xs : 0-2-RAL A n) → {xs≣[] : xs ≡ []} → ⟦ xs ⟧ₙ ≡ zero ∷ []
⟦[]⟧ₙ≡0 []                 = refl
⟦[]⟧ₙ≡0 (      0∷ xs) {()}
⟦[]⟧ₙ≡0 (x     1∷ xs) {()}
⟦[]⟧ₙ≡0 (x , y 2∷ xs) {()}


⟦[]⟧≡0 : ∀ {n A} → (xs : 0-2-RAL A n) → {xs≣[] : xs ≡ []} → ⟦ xs ⟧ ≡ zero ∷ []
⟦[]⟧≡0 {n}    []     {p}  =
    begin
        n <<< (zero ∷ [])
    ≡⟨ {!   !} ⟩
        zero ∷ []
    ∎
⟦[]⟧≡0 (      0∷ xs) {()}
⟦[]⟧≡0 (x     1∷ xs) {()}
⟦[]⟧≡0 (x , y 2∷ xs) {()}
-- identity
⟦[]⟧ₙ≡0 : ∀ {A n} → (xs : 0-2-RAL A n) → xs ≡ [] → ⟦ xs ⟧ₙ ≡ zero
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

⟦[]⟧≡⟦[]⟧ : ∀ {m n A} → ⟦ [] {A} {m} ⟧ ≡ ⟦ [] {A} {n} ⟧
⟦[]⟧≡⟦[]⟧ {m} {n} =
    begin
        2 ^ m * 0
    ≡⟨ *-right-zero (2 ^ m) ⟩
        0
    ≡⟨ sym (*-right-zero (2 ^ n)) ⟩
        2 ^ n * 0
    ∎

splitIndex : ∀ {n A} → (x : BinaryLeafTree A n) → (xs : 0-2-RAL A (suc n)) → ⟦ x 1∷ xs ⟧ ≡ 1 * (2 ^ n) + ⟦ xs ⟧
splitIndex {n} x xs =
    begin
        2 ^ n * suc (2 * ⟦ xs ⟧ₙ)
    ≡⟨ +-*-suc (2 ^ n) (2 * ⟦ xs ⟧ₙ) ⟩
        2 ^ n + 2 ^ n * (2 * ⟦ xs ⟧ₙ)
    ≡⟨ cong (λ w → 2 ^ n + w) (sym (*-assoc (2 ^ n) 2 ⟦ xs ⟧ₙ)) ⟩
        2 ^ n + (2 ^ n * 2) * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ w → 2 ^ n + w * ⟦ xs ⟧ₙ) (*-comm (2 ^ n) 2) ⟩
        2 ^ n + (2 * 2 ^ n) * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ w → w + (2 * 2 ^ n) * ⟦ xs ⟧ₙ) (sym (+-right-identity (2 ^ n))) ⟩
        2 ^ n + 0 + (2 * 2 ^ n) * ⟦ xs ⟧ₙ
    ∎

splitIndex2 : ∀ {n A} → (x : BinaryLeafTree A n) → (y : BinaryLeafTree A n) → (xs : 0-2-RAL A (suc n)) → ⟦ x , y 2∷ xs ⟧ ≡ 2 * (2 ^ n) + ⟦ xs ⟧
splitIndex2 {n} x y xs =
    begin
        2 ^ n * (1 + (1 + (2 * ⟦ xs ⟧ₙ)))
    ≡⟨ +-*-suc (2 ^ n) ((1 + (2 * ⟦ xs ⟧ₙ))) ⟩
        2 ^ n + 2 ^ n * (1 + (2 * ⟦ xs ⟧ₙ))
    ≡⟨ cong (λ w → 2 ^ n + w) (+-*-suc (2 ^ n) (2 * ⟦ xs ⟧ₙ)) ⟩
        2 ^ n + (2 ^ n + 2 ^ n * (2 * ⟦ xs ⟧ₙ))
    ≡⟨ sym (+-assoc (2 ^ n) (2 ^ n) (2 ^ n * (2 * ⟦ xs ⟧ₙ))) ⟩
        2 ^ n + 2 ^ n + 2 ^ n * (2 * ⟦ xs ⟧ₙ)
    ≡⟨ cong (λ w → 2 ^ n + 2 ^ n + w) (sym (*-assoc (2 ^ n) 2 ⟦ xs ⟧ₙ)) ⟩
        2 ^ n + 2 ^ n + (2 ^ n * 2) * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ w → 2 ^ n + 2 ^ n + w * ⟦ xs ⟧ₙ) (*-comm (2 ^ n) 2) ⟩
        2 ^ n + 2 ^ n + (2 * 2 ^ n) * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ w → 2 ^ n + w + (2 * 2 ^ n) * ⟦ xs ⟧ₙ) (sym (+-right-identity (2 ^ n))) ⟩
        2 ^ n + (2 ^ n + 0) + (2 * 2 ^ n) * ⟦ xs ⟧ₙ
    ≡⟨ refl ⟩
        2 * 2 ^ n + (2 * 2 ^ n) * ⟦ xs ⟧ₙ
    ∎

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
