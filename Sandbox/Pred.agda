module Sandbox.Pred where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.List using (List)
open import Data.Vec hiding ([_])
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Num.Bij
open import Data.Num.Bij.Convert hiding ([_]B)


data Term : ℕ → Set where
  var : ∀ {n} → Fin n → Term n
  _∔_ : ∀ {n} → Term n → Term n → Term n

data Pred : ℕ → Set where
  _≋_ : ∀ {n} → Term n → Term n → Pred n
  _⇒_ : ∀ {n} → Pred n → Pred n → Pred n
  All : ∀ {n} → Pred (suc n) → Pred n

record Sig : Set₁ where
    constructor sig
    field
        carrier : Set
        _⊕_ : carrier → carrier → carrier
        _≈_ : carrier → carrier → Set
open Sig

⟦_⟧t : ∀ {n} → Term n → (sig : Sig)
     → let A = carrier sig in Vec A n → A
⟦ var n   ⟧t _               env = lookup n env
⟦ e₁ ∔ e₂ ⟧t (sig A _⊕_ _≈_) env = ⟦ e₁ ⟧t (sig A _⊕_ _≈_) env ⊕ ⟦ e₂ ⟧t (sig A _⊕_ _≈_) env

⟦_⟧ : ∀ {n} → Pred n → (sig : Sig)
    → let A = carrier sig in Vec A n → Set
⟦_⟧ (e₁ ≋ e₂) (sig A _⊕_ _≈_) env = ⟦ e₁ ⟧t (sig A _⊕_ _≈_) env ≈ ⟦ e₂ ⟧t (sig A _⊕_ _≈_) env
⟦_⟧ (p ⇒ q)   signature       env = ⟦ p ⟧ signature env → ⟦ q ⟧ signature env
⟦_⟧ (All p)   signature       env = let A = carrier signature in (x : A) → ⟦ p ⟧ signature (x ∷ env)

≋-trans : Pred zero
≋-trans = All (All (All ((var x ≋ var y) ⇒ ((var y ≋ var z) ⇒ (var x ≋ var z)))))
    where x : Fin 3
          x = suc (suc zero)
          y : Fin 3
          y = suc zero
          z : Fin 3
          z = zero

≋-trans-ℕ : Set
≋-trans-ℕ = ⟦ ≋-trans ⟧ (sig ℕ _+_ _≡_) []

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

 -- loopup
lookup-map : ∀ {i j} → {A : Set i} {B : Set j}
            → (f : A → B) →
            ∀ {n} → (xs : Vec A n) (i : Fin n)
            → lookup i (map f xs) ≡ f (lookup i xs)
lookup-map f [] ()
lookup-map f (x ∷ xs) zero = refl
lookup-map f (x ∷ xs) (suc i) = lookup-map f xs i

--
--    ℕ ⇔ Bij (Zeroless Binary Number)
--

-- mapping Terms
homTerm-ℕ⇒Bij : ∀ {n} (t : Term n) (env : Vec Bij n)
              → ⟦ t ⟧t (sig ℕ _+_ _≡_) (map [_]ℕ env) ≡ [ ⟦ t ⟧t (sig Bij _+B_ _≡_) env ]ℕ
homTerm-ℕ⇒Bij (var i)   env = lookup-map [_]ℕ env i
homTerm-ℕ⇒Bij (t₀ ∔ t₁) env rewrite homTerm-ℕ⇒Bij t₀ env
                                  | homTerm-ℕ⇒Bij t₁ env
                                  = sym ([]ℕ-+B-hom
                                      (⟦ t₀ ⟧t (sig (List DigitB) _+B_ _≡_) env)
                                      (⟦ t₁ ⟧t (sig (List DigitB) _+B_ _≡_) env))

postulate
    []ℕ-injective : ∀ x y → [ x ]ℕ ≡ [ y ]ℕ → x ≡ y

-- mapping Predicates
mutual
    homPred-ℕ⇒Bij : ∀ {n} (p : Pred n) (env : Vec Bij n)
                 → ⟦ p ⟧ (sig ℕ   _+_  _≡_) (map [_]ℕ env)
                 → ⟦ p ⟧ (sig Bij _+B_ _≡_) env
    homPred-ℕ⇒Bij (t₀ ≋ t₁) env proof
        rewrite homTerm-ℕ⇒Bij t₀ env
              | homTerm-ℕ⇒Bij t₁ env
              = []ℕ-injective
                 (⟦ t₀ ⟧t (sig (List DigitB) _+B_ _≡_) env)
                 (⟦ t₁ ⟧t (sig (List DigitB) _+B_ _≡_) env)
                 proof
    homPred-ℕ⇒Bij (p ⇒ q)   env proof x = homPred-ℕ⇒Bij q env (proof (homPred-Bij⇒ℕ p env x))
    homPred-ℕ⇒Bij (All p)   env proof x = homPred-ℕ⇒Bij p (x ∷ env) (proof [ x ]ℕ)

    homPred-Bij⇒ℕ : ∀ {n} (p : Pred n) (env : Vec Bij n)
                  → ⟦ p ⟧ (sig Bij _+B_ _≡_) env
                  → ⟦ p ⟧ (sig ℕ   _+_  _≡_) (map [_]ℕ env)
    homPred-Bij⇒ℕ (t₀ ≋ t₁) env proof
        rewrite homTerm-ℕ⇒Bij t₀ env
              | homTerm-ℕ⇒Bij t₁ env
              = cong [_]ℕ proof
    homPred-Bij⇒ℕ (p ⇒ q)   env proof x = homPred-Bij⇒ℕ q env (proof (homPred-ℕ⇒Bij p env x))
    homPred-Bij⇒ℕ (All p)   env proof x = aux p env proof x
        where
            aux : ∀ {n} → (p : Pred (suc n)) → (env : Vec Bij n)
                  → (pf : ∀ y → ⟦ p ⟧ (sig Bij _+B_ _≡_) (y ∷ env)) → (x : ℕ)
                  →  ⟦ p ⟧ (sig ℕ _+_  _≡_) (x ∷ map [_]ℕ env)
            aux p env proof x  with []ℕ-surjective x
            aux p env proof ._ | (y , refl) = homPred-Bij⇒ℕ p (y ∷ env) (proof y)

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

  ⊕-hom : ∀ (x y : ℕ₁) → [ x ⊕₁ y ]₁₀ ≡ [ x ]₁₀ ⊕₀ [ y ]₁₀

  ≈-hom₀₁ : ∀ {x y : ℕ₁} → [ x ]₁₀ ≈₀ [ y ]₁₀ → x ≈₁ y
  ≈-hom₁₀ : ∀ {x y : ℕ₁} →  x ≈₁ y → [ x ]₁₀ ≈₀ [ y ]₁₀

  []₁₀-surjective : ∀ (x : ℕ₀) → ∃ (λ y → [ y ]₁₀ ≡ x)

homTerm : ∀ {n} (t : Term n) (env : Vec ℕ₁ n)
          →  ⟦ t ⟧t (sig ℕ₀ _⊕₀_ _≈₀_) (map [_]₁₀ env) ≡ [ ⟦ t ⟧t (sig ℕ₁ _⊕₁_ _≈₁_) env ]₁₀
homTerm (var x) env = lookup-map [_]₁₀ env x
homTerm (t₀ ∔ t₁) env rewrite homTerm t₀ env | homTerm t₁ env = sym (⊕-hom _ _)


mutual
  hom₀₁ : ∀ {n} (p : Pred n) (env : Vec ℕ₁ n)
        → ⟦ p ⟧ (sig ℕ₀ _⊕₀_ _≈₀_) (map [_]₁₀ env) → ⟦ p ⟧ (sig ℕ₁ _⊕₁_ _≈₁_) env
  hom₀₁ (t₀ ≋ t₁) env pf rewrite homTerm t₀ env | homTerm t₁ env = ≈-hom₀₁ pf
  hom₀₁ (p₀ ⇒ p₁) env pf pf₀ = hom₀₁ p₁ env (pf (hom₁₀ p₀ env pf₀))
  hom₀₁ (All p) env pf x = hom₀₁ p (x ∷ env) (pf [ x ]₁₀)

  hom₁₀ : ∀ {n} (p : Pred n) (env : Vec ℕ₁ n)
         →  ⟦ p ⟧ (sig ℕ₁ _⊕₁_ _≈₁_) env → ⟦ p ⟧ (sig ℕ₀ _⊕₀_ _≈₀_) (map [_]₁₀ env)
  hom₁₀ (t₀ ≋ t₁) env pf rewrite homTerm t₀ env | homTerm t₁ env = ≈-hom₁₀ pf
  hom₁₀ (p₀ ⇒ p₁) env pf pf₀ = hom₁₀ p₁ env (pf (hom₀₁ p₀ env pf₀))
  hom₁₀ (All p) env pf x = aux p env pf x
    where aux : ∀ {n} → (p : Pred (suc n)) → (env : Vec ℕ₁ n)
                 → (pf : ∀ y → ⟦ p ⟧ (sig ℕ₁ _⊕₁_ _≈₁_) (y ∷ env)) → (x : ℕ₀)
                 →  ⟦ p ⟧ (sig ℕ₀ _⊕₀_ _≈₀_) (x ∷ map [_]₁₀ env)
          aux p env pf x  with []₁₀-surjective x
          aux p env pf ._ | (y , refl) = hom₁₀ p (y ∷ env) (pf y)
