module Data.Num.Pred where

open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin hiding (_+_)
open import Data.Vec
-- open import Relation.Binary.PropositionalEquality

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
        _+_ : carrier → carrier → carrier
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
⟦ t₀ ∔ t₁ ⟧t signature env = let sig A _+_ _≈_ = signature in
    ⟦ t₀ ⟧t signature env + ⟦ t₁ ⟧t signature env

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

import Data.Num.Unary as U
import Data.Num.Binary as B


UnarySig : Signature
UnarySig = sig U.Unary U._+_ U._≈_

BinarySig : Signature
BinarySig = sig B.Binary B._+_ B._≈_

≋-trans : Predicate zero
≋-trans = let   x = var zero
                y = var (suc zero)
                z = var (suc (suc zero))
    in All (All (All (((x ≋ y) ⇒ (y ≋ z)) ⇒ (x ≋ z))))
