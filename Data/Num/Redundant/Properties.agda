module Data.Num.Redundant.Properties where

open import Data.Num.Redundant
open import Data.Num.Redundant.Setoid

open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties.Simple

open import Data.List
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
--open import Relation.Binary.SetoidReasoning
open PropEq.≡-Reasoning


⊕-comm : (a b : Digit) → a ⊕ b ≡ b ⊕ a
⊕-comm zero zero = refl
⊕-comm zero one = refl
⊕-comm zero two = refl
⊕-comm one zero = refl
⊕-comm one one = refl
⊕-comm one two = refl
⊕-comm two zero = refl
⊕-comm two one = refl
⊕-comm two two = refl

⊕-assoc : (a b c : Digit) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
⊕-assoc zero b c = refl
⊕-assoc one zero c = refl
⊕-assoc one one zero = refl
⊕-assoc one one one = refl
⊕-assoc one one two = refl
⊕-assoc one two zero = refl
⊕-assoc one two one = refl
⊕-assoc one two two = refl
⊕-assoc two zero c = refl
⊕-assoc two one zero = refl
⊕-assoc two one one = refl
⊕-assoc two one two = refl
⊕-assoc two two zero = refl
⊕-assoc two two one = refl
⊕-assoc two two two = refl

⊕-right-identity : (a : Digit) → a ⊕ zero ≡ a
⊕-right-identity zero = refl
⊕-right-identity one = refl
⊕-right-identity two = refl

⊙-comm : (a b : Digit) → a ⊙ b ≡ b ⊙ a
⊙-comm zero zero = refl
⊙-comm zero one = refl
⊙-comm zero two = refl
⊙-comm one zero = refl
⊙-comm one one = refl
⊙-comm one two = refl
⊙-comm two zero = refl
⊙-comm two one = refl
⊙-comm two two = refl

>>0≡0 : ∀ {a} → (a≡0 : a ~ zero ∷ []) → >> a ~ zero ∷ []
>>0≡0 {[]}     (a≡0) = eq refl
>>0≡0 {x ∷ xs} (eq x∷xs≡0) = eq (
    begin
        toℕ (x ∷ xs) +ℕ (toℕ (x ∷ xs) +ℕ 0)
    ≡⟨ cong (λ w → w +ℕ (w +ℕ 0)) x∷xs≡0 ⟩
        0 +ℕ (0 +ℕ 0)
    ≡⟨ refl ⟩
        2 * 0
    ≡⟨ *-right-zero 2 ⟩
        0
    ∎)

{-
    begin
        {!   !}
    ≈⟨ {!   !} ⟩
        {!   !}
    ≈⟨ {!   !} ⟩
        {!   !}
    ≈⟨ {!   !} ⟩
        {!   !}
    ≈⟨ {!   !} ⟩
        {!   !}
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
