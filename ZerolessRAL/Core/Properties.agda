module ZerolessRAL.Core.Properties where

open import BuildingBlock
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
open import ZerolessRAL.Core

open import Data.Nat
open import Data.Nat.Etc
open import Data.Nat.Properties.Simple

open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning
--------------------------------------------------------------------------------
-- On ⟦_⟧ and ⟦_⟧ₙ

-- identity
⟦[]⟧ₙ≡0 : ∀ {A n} → (xs : 1-2-RAL A n) → xs ≡ [] → ⟦ xs ⟧ₙ ≡ 0
⟦[]⟧ₙ≡0 []            p  = refl
⟦[]⟧ₙ≡0 (x 1∷ xs)     ()
⟦[]⟧ₙ≡0 (x , y 2∷ xs) ()

⟦[]⟧≡0 : ∀ {n A} → (xs : 1-2-RAL A n) → xs ≡ [] → ⟦ xs ⟧ ≡ 0
⟦[]⟧≡0 {zero}     [] p  = refl
⟦[]⟧≡0 {suc n}    [] p  = *-right-zero (2 * 2 ^ n)
⟦[]⟧≡0 (x     1∷ xs) ()
⟦[]⟧≡0 (x , y 2∷ xs) ()

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
