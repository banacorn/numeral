module Sandbox.Pred where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Product hiding (map)
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

postulate
  ℕ₀ : Set
  _⊕₀_ : ℕ₀ → ℕ₀ → ℕ₀
  _≈₀_ : ℕ₀ → ℕ₀ → Set
  
  ℕ₁ : Set
  _⊕₁_ : ℕ₁ → ℕ₁ → ℕ₁
  _≈₁_ : ℕ₁ → ℕ₁ → Set

  [_]₀₁ : ℕ₀ → ℕ₁
  [_]₁₀ : ℕ₁ → ℕ₀

   -- naturality of lookup.
   
  lookup-map : ∀ {i j} → {A : Set i} {B : Set j}
               → (f : A → B) →
               ∀ {n} → (xs : Vec A n) (i : Fin n)
               → lookup i (map f xs) ≡ f (lookup i xs)

  ⊕-hom : ∀ (x y : ℕ₁) → [ x ⊕₁ y ]₁₀ ≡ [ x ]₁₀ ⊕₀ [ y ]₁₀

  ≈-hom₀₁ : ∀ {x y : ℕ₁} → [ x ]₁₀ ≈₀ [ y ]₁₀ → x ≈₁ y
  ≈-hom₁₀ : ∀ {x y : ℕ₁} →  x ≈₁ y → [ x ]₁₀ ≈₀ [ y ]₁₀

  []₁₀-surjective : ∀ (x : ℕ₀) → ∃ (λ y → [ y ]₁₀ ≡ x)

homTerm : ∀ {n} (t : Term n) (env : Vec ℕ₁ n)
          →  ⟦ t ⟧t (ℕ₀ , _⊕₀_ , _≈₀_) (map [_]₁₀ env) ≡ [ ⟦ t ⟧t (ℕ₁ , _⊕₁_ , _≈₁_) env ]₁₀
homTerm (var x) env = lookup-map [_]₁₀ env x
homTerm (t₀ ∔ t₁) env rewrite homTerm t₀ env | homTerm t₁ env = sym (⊕-hom _ _)


mutual
  hom₀₁ : ∀ {n} (p : Pred n) (env : Vec ℕ₁ n)
        → ⟦ p ⟧ (ℕ₀ , _⊕₀_ , _≈₀_) (map [_]₁₀ env) → ⟦ p ⟧ (ℕ₁ , _⊕₁_ , _≈₁_) env
  hom₀₁ (t₀ ≋ t₁) env pf rewrite homTerm t₀ env | homTerm t₁ env = ≈-hom₀₁ pf
  hom₀₁ (p₀ ⇒ p₁) env pf pf₀ = hom₀₁ p₁ env (pf (hom₁₀ p₀ env pf₀))
  hom₀₁ (All p) env pf x = hom₀₁ p (x ∷ env) (pf [ x ]₁₀)

  hom₁₀ : ∀ {n} (p : Pred n) (env : Vec ℕ₁ n)
         →  ⟦ p ⟧ (ℕ₁ , _⊕₁_ , _≈₁_) env → ⟦ p ⟧ (ℕ₀ , _⊕₀_ , _≈₀_) (map [_]₁₀ env)
  hom₁₀ (t₀ ≋ t₁) env pf rewrite homTerm t₀ env | homTerm t₁ env = ≈-hom₁₀ pf
  hom₁₀ (p₀ ⇒ p₁) env pf pf₀ = hom₁₀ p₁ env (pf (hom₀₁ p₀ env pf₀))
  hom₁₀ (All p) env pf x = aux p env pf x
    where aux : ∀ {n} → (p : Pred (suc n)) → (env : Vec ℕ₁ n)
                 → (pf : ∀ y → ⟦ p ⟧ (ℕ₁ , _⊕₁_ , _≈₁_) (y ∷ env)) → (x : ℕ₀)
                 →  ⟦ p ⟧ (ℕ₀ , _⊕₀_ , _≈₀_) (x ∷ map [_]₁₀ env)
          aux p env pf x  with []₁₀-surjective x
          aux p env pf ._ | (y , refl) = hom₁₀ p (y ∷ env) (pf y)
