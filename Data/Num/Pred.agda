module Data.Num.Pred where

open import Data.Num
open import Data.Num.Properties
open import Data.Num.Bijection

open import Data.Nat
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Vec
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (True; fromWitness)

infixl 6 _∔_

data Term : ℕ → Set where
    var : ∀ {n} → Fin n → Term n
    _∔_ : ∀ {n} → Term n → Term n → Term n

infix 4 _≋_

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

ℕ-sig : Signature
ℕ-sig = sig ℕ _+_ _≡_

Num-sig : (b d o : ℕ) → True (Surjective? b d o) → Signature
Num-sig b d o pf = sig (Num b d o) (_⊹_ {surj = pf}) _≡_

BijN-sig : ℕ → Signature
BijN-sig b = sig (BijN b) (_⊹_ {surj = fromWitness (BijN⇒Surjective b)}) _≡_


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


module Example-1 where
    ≋-trans : Predicate zero
    ≋-trans = let   x = var zero
                    y = var (suc zero)
                    z = var (suc (suc zero))
        in All (All (All (((x ≋ y) ⇒ (y ≋ z)) ⇒ (x ≋ z))))

    ≋-trans-ℕ : Set
    ≋-trans-ℕ = ⟦ ≋-trans ⟧ ℕ-sig []

    ≋-trans-Num : (b d o : ℕ) → True (Surjective? b d o) → Set
    ≋-trans-Num b d o pf = ⟦ ≋-trans ⟧ (Num-sig b d o pf) []

    ≋-trans-BijN : ℕ → Set
    ≋-trans-BijN b = ⟦ ≋-trans ⟧ (BijN-sig b) []

-- lemma for env
lookup-map : ∀ {i j} → {A : Set i} {B : Set j}
           → (f : A → B) →
           ∀ {n} → (xs : Vec A n) (i : Fin n)
           → lookup i (map f xs) ≡ f (lookup i xs)
lookup-map f []       ()
lookup-map f (x ∷ xs) zero    = refl
lookup-map f (x ∷ xs) (suc i) = lookup-map f xs i





------------------------------------------------------------------------
-- toℕ : preserving structures of terms and predicates
------------------------------------------------------------------------

toℕ-term-homo : ∀ {b n}
    → (t : Term n)
    → (env : Vec (BijN b) n)
    → ⟦ t ⟧T ℕ-sig (map toℕ env) ≡ toℕ (⟦ t ⟧T (BijN-sig b) env)
toℕ-term-homo     (var i)   env = lookup-map toℕ env i
toℕ-term-homo {b} (t₁ ∔ t₂) env
    rewrite toℕ-term-homo t₁ env | toℕ-term-homo t₂ env
    = sym (toℕ-⊹-homo
            (⟦ t₁ ⟧T (BijN-sig b) env)
            (⟦ t₂ ⟧T (BijN-sig b) env))


mutual
    toℕ-pred-ℕ⇒Bij : ∀ {b n}
                → (pred : Predicate n)
                → (env  : Vec (Bij (suc b)) n)
                → ⟦ pred ⟧ ℕ-sig            (map toℕ env)
                → ⟦ pred ⟧ (BijN-sig (suc b)) env
    toℕ-pred-ℕ⇒Bij {b} (t₁ ≋ t₂) env ⟦t₁≈t₂⟧ℕ
        rewrite toℕ-term-homo t₁ env | toℕ-term-homo t₂ env -- ⟦ t₁ ⟧T ℕ-sig (map toℕ env) ≡ toℕ (⟦ t₁ ⟧T (Bij-sig (suc b)) env)
        = toℕ-injective (⟦ t₁ ⟧T (BijN-sig (suc b)) env) (⟦ t₂ ⟧T (BijN-sig (suc b)) env) ⟦t₁≈t₂⟧ℕ
    toℕ-pred-ℕ⇒Bij (p ⇒ q)   env ⟦p→q⟧ℕ ⟦p⟧B = toℕ-pred-ℕ⇒Bij q env (⟦p→q⟧ℕ (toℕ-pred-Bij⇒ℕ p env ⟦p⟧B))
    toℕ-pred-ℕ⇒Bij (All p)   env ⟦λx→p⟧ℕ x = toℕ-pred-ℕ⇒Bij p (x ∷ env) (⟦λx→p⟧ℕ (toℕ x))

    toℕ-pred-Bij⇒ℕ : ∀ {b n}
                → (pred : Predicate n)
                → (env  : Vec (Bij (suc b)) n)
                → ⟦ pred ⟧ (BijN-sig (suc b)) env
                → ⟦ pred ⟧ ℕ-sig             (map toℕ env)
    toℕ-pred-Bij⇒ℕ (t₁ ≋ t₂) env ⟦t₁≈t₂⟧B
        rewrite toℕ-term-homo t₁ env | toℕ-term-homo t₂ env
        = cong toℕ ⟦t₁≈t₂⟧B
    toℕ-pred-Bij⇒ℕ (p ⇒ q) env ⟦p→q⟧B ⟦p⟧ℕ = toℕ-pred-Bij⇒ℕ q env (⟦p→q⟧B (toℕ-pred-ℕ⇒Bij p env ⟦p⟧ℕ))
    toℕ-pred-Bij⇒ℕ {b} (All p) env ⟦λx→p⟧B x
        rewrite (sym (toℕ-fromℕ b x)) -- rewritting "x" to "toℕ (fromℕ x)"
        = toℕ-pred-Bij⇒ℕ p (fromℕ x ∷ env) (⟦λx→p⟧B (fromℕ x))


-- fromℕ-term-homo : ∀ {b n}
--     → (term : Term n)
--     → (env : Vec ℕ n)
--     → ⟦ term ⟧T (Bij-sig (suc b)) (map fromℕ env) ≡ fromℕ (⟦ term ⟧T ℕ-sig env)
-- fromℕ-term-homo         (var i)   env = lookup-map fromℕ env i
-- fromℕ-term-homo {b} {n} (t₁ ∔ t₂) env
--     rewrite fromℕ-term-homo {b} {n} t₁ env | fromℕ-term-homo {b} {n} t₂ env
--     = sym (fromℕ-⊹-homo (⟦ t₁ ⟧T (sig ℕ _+_ _≡_) env) (⟦ t₂ ⟧T (sig ℕ _+_ _≡_) env))
--
--
-- ------------------------------------------------------------------------
--
-- open import Data.Nat.Properties.Simple
--
--
-- testExtract : {pred : Predicate 0}
--         → ⟦ pred ⟧ ℕ-sig []
--         → Predicate 0
-- testExtract {pred} ⟦pred⟧ℕ = pred
--
-- ∔-comm : Predicate 0
-- ∔-comm = testExtract {All (All (var (suc zero) ∔ var zero ≋ var zero ∔ var (suc zero)))} +-comm
--
-- ∔-assoc : Predicate 0
-- ∔-assoc = testExtract {All (All (All (var (suc (suc zero)) ∔ var (suc zero) ∔ var zero ≋ var (suc (suc zero)) ∔ (var (suc zero) ∔ var zero))))} +-assoc
-- ∔-assoc = testExtract {All (All (All (var (suc (suc zero)) ∔ var (suc zero) ∔ var zero ≋ var (suc (suc zero)) ∔ (var (suc zero) ∔ var zero))))} +-assoc
