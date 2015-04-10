module Pred where

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Pred : ℕ → Set where
  _≋_ : ∀ {n} → Fin n → Fin n → Pred n 
  _⇒_ : ∀ {n} → Pred n → Pred n → Pred n
  All : ∀ {n} → Pred (suc n) → Pred n
  
Sig : Set₁
Sig = Σ[ A ∈ Set ] (A → A → Set)

⟦_⟧ : ∀ {n} → Pred n 
     → (sig : Sig) → Vec (proj₁ sig) n → Set
⟦ n₁ ≋ n₂ ⟧ (A , _≈_) env = (lookup n₁ env) ≈ (lookup n₂ env) 
⟦ p ⇒ q ⟧ sig env = ⟦ p ⟧ sig env → ⟦ q ⟧ sig env
⟦ All p ⟧ (A , ≈) env = (x : A) → ⟦ p ⟧ (A , ≈) (x ∷ env)

≋-trans : Pred zero
≋-trans = All (All (All ((x ≋ y) ⇒ ((y ≋ z) ⇒ (x ≋ z)))))
   where x : Fin 3
         x = suc (suc zero)
         y : Fin 3
         y = suc zero
         z : Fin 3
         z = zero

≋-trans-ℕ : Set
≋-trans-ℕ = ⟦ ≋-trans ⟧ (ℕ , _≡_) []

  -- ≋-trans-ℕ evaluates to
  -- (x x₁ x₂ : ℕ) → x ≡ x₁ → x₁ ≡ x₂ → x ≡ x₂

{- Goal: to show that
   ∀ p → ⟦ p ⟧ (ℕ , _≡_) [] → ⟦ p ⟧ (Redundant , _≈_) []
-}