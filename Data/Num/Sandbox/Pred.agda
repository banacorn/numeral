module Data.Num.Sandbox.Pred where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality

-- open import Data.Num.Unary

data Term : ℕ → Set where
    var : ∀ {n} → Fin n → Term n
    _∔_ : ∀ {n} → Term n → Term n → Term n

data Predicate : ℕ → Set where
    -- equality
    _≋_ : ∀ {n} → (t₀ : Term n) → (t₁ : Term n) → Predicate n
    -- implication
    _⇒_ : ∀ {n} → (p₀ : Predicate n) → (p₁ : Predicate n) → Predicate n
    -- ∀, introduces new variable
    All : ∀ {n} → (p : Predicate (suc n)) → Predicate n

record Signature : Set₁ where
    constructor sig
    field
        carrier : Set
        _⊕_ : carrier → carrier → carrier
        _≈_ : carrier → carrier → Set
open Signature

Env : Set → ℕ → Set
Env = Vec

-- the decoder
⟦_⟧t : ∀ {n}
    → Term n
    → (sig : Signature)
    → Env (carrier sig) n
    → carrier sig
⟦ var x   ⟧t signature env = lookup x env
⟦ t₀ ∔ t₁ ⟧t signature env = let sig A _⊕_ _≈_ = signature in
    ⟦ t₀ ⟧t signature env ⊕ ⟦ t₁ ⟧t signature env

⟦_⟧ : ∀ {n}
    → Predicate n
    → (sig : Signature)
    → Env (carrier sig) n
    → Set
⟦ t₀ ≋ t₁ ⟧ signature env = let sig _ _ _≈_ = signature in
    ⟦ t₀ ⟧t signature env ≈ ⟦ t₁ ⟧t signature env
⟦ p₀ ⇒ p₁ ⟧ signature env =
    ⟦ p₀ ⟧ signature env → ⟦ p₁ ⟧ signature env
⟦ All pred ⟧ signature env =
    (x : carrier signature) → ⟦ pred ⟧ signature (x ∷ env)

import Data.Num.Bijective as Bij
import Data.Num.Bijective.Properties

BijSig : ℕ → Signature
BijSig b = sig (Bij.Num b) Bij.add _≡_

ℕSig : Signature
ℕSig = sig ℕ _+_ _≡_

≋-trans : Predicate zero
≋-trans = let   x = var zero
                y = var (suc zero)
                z = var (suc (suc zero))
    in All (All (All (((x ≋ y) ⇒ (y ≋ z)) ⇒ (x ≋ z))))

≋-trans-ℕ : Set
≋-trans-ℕ = ⟦ ≋-trans ⟧ ℕSig []

≋-trans-Bij : ℕ → Set
≋-trans-Bij b = ⟦ ≋-trans ⟧ (BijSig b) []


-- lemma for env
lookup-map : ∀ {i j} → {A : Set i} {B : Set j}
           → (f : A → B) →
           ∀ {n} → (xs : Vec A n) (i : Fin n)
           → lookup i (map f xs) ≡ f (lookup i xs)
lookup-map f []       ()
lookup-map f (x ∷ xs) zero    = refl
lookup-map f (x ∷ xs) (suc i) = lookup-map f xs i

postulate
    toℕ-add-hom : ∀ {b} (xs ys : Bij.Num b) → Bij.toℕ (Bij.add xs ys) ≡ Bij.toℕ xs + Bij.toℕ ys
    toℕ-injective : ∀ {b} (xs ys : Bij.Num b) → Bij.toℕ xs ≡ Bij.toℕ ys → xs ≡ ys
    toℕ-surjective : ∀ {b} n → ∃ (λ xs → Bij.toℕ {b} xs ≡ n)

homTerm-ℕ⇒Bij : ∀ {b n}
    → (t : Term n)
    → (env : Vec (Bij.Num b) n)
    → ⟦ t ⟧t ℕSig (map Bij.toℕ env) ≡ Bij.toℕ (⟦ t ⟧t (BijSig b) env)
homTerm-ℕ⇒Bij     (var i)   env = lookup-map Bij.toℕ env i
homTerm-ℕ⇒Bij {b} (t₀ ∔ t₁) env rewrite homTerm-ℕ⇒Bij t₀ env
                                  | homTerm-ℕ⇒Bij t₁ env
                                  = sym (toℕ-add-hom
                                      (⟦ t₀ ⟧t (BijSig b) env)
                                      (⟦ t₁ ⟧t (BijSig b) env))

mutual
    homPred-ℕ⇒Bij : ∀ {b n}
                    → (p : Predicate n)
                    → (env : Vec (Bij.Num b) n)
                    → ⟦ p ⟧ ℕSig       (map Bij.toℕ env)
                    → ⟦ p ⟧ (BijSig b) env
    homPred-ℕ⇒Bij {b} (t₀ ≋ t₁) env proof
        rewrite homTerm-ℕ⇒Bij t₀ env
              | homTerm-ℕ⇒Bij t₁ env
              = toℕ-injective
                 (⟦ t₀ ⟧t (BijSig b) env)
                 (⟦ t₁ ⟧t (BijSig b) env)
                 proof
    homPred-ℕ⇒Bij (p ⇒ q) env proof x = homPred-ℕ⇒Bij q env (proof (homPred-Bij⇒ℕ p env x))
    homPred-ℕ⇒Bij (All p)  env proof x = homPred-ℕ⇒Bij p (x ∷ env) (proof (Bij.toℕ x))

    homPred-Bij⇒ℕ : ∀ {b n}
                    → (p : Predicate n)
                    → (env : Vec (Bij.Num b) n)
                    → ⟦ p ⟧ (BijSig b) env
                    → ⟦ p ⟧ ℕSig      (map Bij.toℕ env)
    homPred-Bij⇒ℕ (t₀ ≋ t₁) env proof
        rewrite homTerm-ℕ⇒Bij t₀ env
              | homTerm-ℕ⇒Bij t₁ env
              = cong Bij.toℕ proof
    homPred-Bij⇒ℕ (p ⇒ q) env proof x = homPred-Bij⇒ℕ q env (proof (homPred-ℕ⇒Bij p env x))
    homPred-Bij⇒ℕ (All p)  env proof x = aux p env proof x
        where
            aux : ∀ {b n} → (p : Predicate (suc n)) → (env : Vec (Bij.Num b) n)
                  → (pf : ∀ y → ⟦ p ⟧ (BijSig b) (y ∷ env)) → (x : ℕ)
                  →  ⟦ p ⟧ ℕSig (x ∷ map Bij.toℕ env)
            aux {b} p env proof x with toℕ-surjective {b} x
            aux p env proof .(Bij.toℕ y) | y , refl = homPred-Bij⇒ℕ p (y ∷ env) (proof y)
