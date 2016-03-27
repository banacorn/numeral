module Data.Num.Pred where

open import Data.Num.Bijective
open import Data.Num.Bijective.Properties

open import Data.Nat
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Vec
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality

data Term : ℕ → Set where
    var : ∀ {n} → Fin n → Term n
    _∔_ : ∀ {n} → Term n → Term n → Term n

data Predicate : ℕ → Set where
    -- equality
    _≋_ : ∀ {n} → (t₁ : Term n) → (t₂ : Term n) → Predicate n
    -- implication
    _⇒_ : ∀ {n} → (p₁ : Predicate n) → (p₂ : Predicate n) → Predicate n
    -- ∀, introduces new variable
    All : ∀ {n} → (p : Predicate (suc n)) → Predicate n

record Signature : Set₁ where
    constructor sig
    field
        carrier : Set
        _⊕_ : carrier → carrier → carrier
        _≈_ : carrier → carrier → Set
open Signature


Bij-sig : ℕ → Signature
Bij-sig b = sig (Bij b) _⊹_ _≡_

ℕ-sig : Signature
ℕ-sig = sig ℕ _+_ _≡_


Env : Set → ℕ → Set
Env = Vec

-- the decoder
⟦_⟧T : ∀ {n}
    → Term n
    → (sig : Signature)
    → Vec (carrier sig) n
    → carrier sig
⟦ var i         ⟧T _                env = lookup i env
⟦ term₁ ∔ term₂ ⟧T (sig A _⊕_ _≈_) env = ⟦ term₁ ⟧T (sig A _⊕_ _≈_) env ⊕ ⟦ term₂ ⟧T (sig A _⊕_ _≈_) env

⟦_⟧ : ∀ {n}
    → Predicate n
    → (sig : Signature)
    → Env (carrier sig) n
    → Set
⟦_⟧ (term₁ ≋ term₂) (sig A _⊕_ _≈_) env = ⟦ term₁ ⟧T (sig A _⊕_ _≈_) env ≈ ⟦ term₂ ⟧T (sig A _⊕_ _≈_) env
⟦_⟧ (p ⇒ q)         signature       env = ⟦ p ⟧ signature env → ⟦ q ⟧ signature env
⟦_⟧ (All p)          signature       env = (x : carrier signature) → ⟦ p ⟧ signature (x ∷ env)


module Example where
    ≋-trans : Predicate zero
    ≋-trans = let   x = var zero
                    y = var (suc zero)
                    z = var (suc (suc zero))
        in All (All (All (((x ≋ y) ⇒ (y ≋ z)) ⇒ (x ≋ z))))

    ≋-trans-ℕ : Set
    ≋-trans-ℕ = ⟦ ≋-trans ⟧ ℕ-sig []

    ≋-trans-Bij : ℕ → Set
    ≋-trans-Bij b = ⟦ ≋-trans ⟧ (Bij-sig b) []

-- lemma for env
lookup-map : ∀ {i j} → {A : Set i} {B : Set j}
           → (f : A → B) →
           ∀ {n} → (xs : Vec A n) (i : Fin n)
           → lookup i (map f xs) ≡ f (lookup i xs)
lookup-map f []       ()
lookup-map f (x ∷ xs) zero    = refl
lookup-map f (x ∷ xs) (suc i) = lookup-map f xs i

-- postulate
--     toℕ-surjective : ∀ {b} n → ∃ (λ xs → Bij.toℕ {b} xs ≡ n)

--  toℕ preserves interpretations of Terms
toℕ-term-homo : ∀ {b n}
    → (t : Term n)
    → (env : Vec (Bij (suc b)) n)
    → ⟦ t ⟧T ℕ-sig (map toℕ env) ≡ toℕ (⟦ t ⟧T (Bij-sig (suc b)) env)
toℕ-term-homo     (var i)   env = lookup-map toℕ env i
toℕ-term-homo {b} (t₀ ∔ t₁) env
    rewrite toℕ-term-homo t₀ env | toℕ-term-homo t₁ env
    = sym (toℕ-⊹-homo
            (⟦ t₀ ⟧T (Bij-sig (suc b)) env)
            (⟦ t₁ ⟧T (Bij-sig (suc b)) env))



--  toℕ preserves interpretations of Predicates
mutual
    pred-ℕ⇒Bij : ∀ {b n}
                → (pred : Predicate n)
                → (env  : Vec (Bij (suc b)) n)
                → ⟦ pred ⟧ ℕ-sig            (map toℕ env)
                → ⟦ pred ⟧ (Bij-sig (suc b)) env
    pred-ℕ⇒Bij {b} (t₁ ≋ t₂) env ⟦t₁≈t₂⟧B
        rewrite toℕ-term-homo t₁ env | toℕ-term-homo t₂ env
        = toℕ-injective (⟦ t₁ ⟧T (Bij-sig (suc b)) env) (⟦ t₂ ⟧T (Bij-sig (suc b)) env) ⟦t₁≈t₂⟧B
    pred-ℕ⇒Bij (p ⇒ q)   env ⟦p→q⟧ℕ ⟦p⟧B = pred-ℕ⇒Bij q env (⟦p→q⟧ℕ (pred-Bij⇒ℕ p env ⟦p⟧B))
    pred-ℕ⇒Bij (All p)   env ⟦λx→p⟧ℕ x = pred-ℕ⇒Bij p (x ∷ env) (⟦λx→p⟧ℕ (toℕ x))

    pred-Bij⇒ℕ : ∀ {b n}
                → (pred : Predicate n)
                → (env  : Vec (Bij (suc b)) n)
                → ⟦ pred ⟧ (Bij-sig (suc b)) env
                → ⟦ pred ⟧ ℕ-sig             (map toℕ env)
    pred-Bij⇒ℕ (t₁ ≋ t₂) env ⟦t₁≈t₂⟧B
        rewrite toℕ-term-homo t₁ env | toℕ-term-homo t₂ env
        = cong toℕ ⟦t₁≈t₂⟧B
    pred-Bij⇒ℕ (p ⇒ q) env ⟦p→q⟧B ⟦p⟧ℕ = pred-Bij⇒ℕ q env (⟦p→q⟧B (pred-ℕ⇒Bij p env ⟦p⟧ℕ))
    pred-Bij⇒ℕ {b} (All p) env ⟦λx→p⟧B x
        rewrite (sym (toℕ-fromℕ b x)) -- rewritting "x" to "toℕ (fromℕ x)"
        = pred-Bij⇒ℕ p (fromℕ x ∷ env) (⟦λx→p⟧B (fromℕ x))
