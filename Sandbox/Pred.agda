module Pred where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Term : ℕ → Set where
  var : ∀ {n} → Fin n → Term n
  _∔_ : ∀ {n} → Term n → Term n → Term n
  
data Pred : ℕ → Set where
  _≋_ : ∀ {n} → Term n → Term n → Pred n
  _⇒_ : ∀ {n} → Pred n → Pred n → Pred n
  All : ∀ {n} → Pred (suc n) → Pred n
  
Sig : Set₁
Sig = Σ[ A ∈ Set ] ((A → A → A) × (A → A → Set))

⟦_⟧t : ∀ {n} → Term n → (sig : Sig)
       → let (A , _) = sig in Vec A n → A
⟦ var n ⟧t (A , _⊕_ , _≈_) env = lookup n env
⟦ e₁ ∔ e₂ ⟧t (A , _⊕_ , _≈_) env = ⟦ e₁ ⟧t (A , _⊕_ , _≈_) env ⊕ ⟦ e₂ ⟧t (A , _⊕_ , _≈_) env


⟦_⟧ : ∀ {n} → Pred n 
     → (sig : Sig) → Vec (proj₁ sig) n → Set
⟦ e₁ ≋ e₂ ⟧ (A , ⊕ , _≈_) env = ⟦ e₁ ⟧t (A , ⊕ , _≈_) env ≈ ⟦ e₂ ⟧t (A , ⊕ , _≈_) env
⟦ p ⇒ q ⟧ sig env = ⟦ p ⟧ sig env → ⟦ q ⟧ sig env
⟦ All p ⟧ (A , ∔≈) env = (x : A) → ⟦ p ⟧ (A , ∔≈) (x ∷ env)


≋-trans : Pred zero
≋-trans = All (All (All ((var x ≋ var y) ⇒ ((var y ≋ var z) ⇒ (var x ≋ var z)))))
   where x : Fin 3
         x = suc (suc zero)
         y : Fin 3
         y = suc zero
         z : Fin 3
         z = zero

≋-trans-ℕ : Set
≋-trans-ℕ = ⟦ ≋-trans ⟧ (ℕ , _+_ , _≡_) []

  -- ≋-trans-ℕ evaluates to
  -- (x x₁ x₂ : ℕ) → x ≡ x₁ → x₁ ≡ x₂ → x ≡ x₂

+-assoc : Pred zero
+-assoc = All (All (All (((var x ∔ var y) ∔ var z) ≋ (var x ∔ (var y ∔ var z)))))
   where x : Fin 3
         x = suc (suc zero)
         y : Fin 3
         y = suc zero
         z : Fin 3
         z = zero
         
{- Goal: to show that
   ∀ p → ⟦ p ⟧ (ℕ , _≡_) [] → ⟦ p ⟧ (Redundant , _≈_) []
-}
