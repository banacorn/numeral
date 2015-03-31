module Data.Num.Redundant.Properties where

open import Data.Num.Nat
open import Data.Num.Redundant
open import Data.Num.Redundant.Setoid

open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Nat.Etc
open import Data.Nat.Properties.Simple

open import Data.List
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
--open import Relation.Binary.SetoidReasoning
--    renaming (begin⟨_⟩_ to beginRel⟨_⟩_; _∎ to _∎Rel)
--    hiding (_≡⟨_⟩_)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------
--  Digits
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
--  Sequence of Digits
--------------------------------------------------------------------------------

-- >> 0 ≈ 0
>>-zero : (a : Redundant) → a ≈ zero ∷ [] → >> a ≈ zero ∷ []
>>-zero []       p           = eq refl
>>-zero (x ∷ xs) (eq x∷xs≈0) = eq (
    begin
        2 * ⟦ x ∷ xs ⟧
    ≡⟨ cong (λ w → 2 * w) x∷xs≈0 ⟩
        2 * 0
    ≡⟨ *-right-zero 2 ⟩
        0
    ∎)

-- << 0 ≈ 0
<<-zero : (a : Redundant) → a ≈ zero ∷ [] → << a ≈ zero ∷ []
<<-zero []       p           = eq refl
<<-zero (x ∷ xs) (eq x∷xs≈0) = eq (⟦x∷xs⟧≡0⇒⟦xs⟧≡0 x xs x∷xs≈0)
    where   ⟦x∷xs⟧≡0⇒⟦xs⟧≡0 : (d : Digit) → (xs : Redundant) → ⟦ d ∷ xs ⟧ ≡ 0 → ⟦ xs ⟧ ≡ 0
            ⟦x∷xs⟧≡0⇒⟦xs⟧≡0 d []          p = refl
            ⟦x∷xs⟧≡0⇒⟦xs⟧≡0 zero (x ∷ xs) p = no-zero-divisor 2 (⟦ x ⟧ +ℕ 2 * ⟦ xs ⟧) (λ ()) p
            ⟦x∷xs⟧≡0⇒⟦xs⟧≡0 one  (x ∷ xs) p = contradiction p (λ ())
            ⟦x∷xs⟧≡0⇒⟦xs⟧≡0 two  (x ∷ xs) p = contradiction p (λ ())


{-

    begin⟨ ? ⟩
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
