module Sandbox.Pred where

open import Data.Num
open import Data.Num.Properties

open import Data.Nat
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Vec
open import Relation.Nullary.Decidable using (True; fromWitness)
open import Relation.Binary.PropositionalEquality hiding ([_])
-- open import Relation.Binary
open ≡-Reasoning

data Term : ℕ → Set where
    var : ∀ {n}
        → Fin n     -- the index of this variable
        → Term n
    _∔_ : ∀ {n} → Term n → Term n → Term n


data Pred : ℕ → Set where
  _≣_ : ∀ {n} → Term n → Term n → Pred n
  _⇒_ : ∀ {n} → Pred n → Pred n → Pred n
  -- captures 1 free variable in the Pred
  All : ∀ {n} → Pred (suc n) → Pred n

record Signature : Set₁ where
    constructor signature
    field
        carrier : Set
        _⊕_ : carrier → carrier → carrier
        _≈_ : carrier → carrier → Set

open Signature

-- signatures
ℕ-sig : Signature
ℕ-sig = signature ℕ _+_ _≡_

Num-sig : (b d o : ℕ) → True (Surjective? b d o) → Signature
Num-sig b d o surj = signature (Num b d o) (_⊹_ {surj = surj}) _≋_

⟦_⟧Term : ∀ {n}
    → Term n
    → (sig : Signature)
    → let A = carrier sig in Vec A n
    → A
⟦ var x ⟧Term sig env = lookup x env
⟦ a ∔ b ⟧Term sig env = let (signature A _⊕_ _≈_) = sig in
                        (⟦ a ⟧Term sig env) ⊕ (⟦ b ⟧Term sig env)

⟦_⟧ : ∀ {n}
    → Pred n
    → (sig : Signature)
    → Vec (carrier sig) n
    → Set
⟦ p ≣ q ⟧ sig env = let (signature carrier _⊕_ _≈_) = sig in
                    ⟦ p ⟧Term sig env ≈ ⟦ q ⟧Term sig env
⟦ p ⇒ q ⟧ sig env = ⟦ p ⟧ sig env → ⟦ q ⟧ sig env
⟦ All p ⟧ sig env = ∀ x → ⟦ p ⟧ sig (x ∷ env)

-- lemma for env
lookup-map : ∀ {i j} → {A : Set i} {B : Set j}
           → (f : A → B) →
           ∀ {n} → (xs : Vec A n) (i : Fin n)
           → lookup i (map f xs) ≡ f (lookup i xs)
lookup-map f []        ()
lookup-map f (x ∷ env) zero    = refl
lookup-map f (x ∷ env) (suc i) = lookup-map f env i

toℕ-term-homo : ∀ {b d o}
    → {surj : True (Surjective? b d o)}
    → ∀ {n}
    → (t : Term n)
    → (env : Vec (Num b d o) n)
    → ⟦ t ⟧Term ℕ-sig (map toℕ env) ≡ toℕ (⟦ t ⟧Term (Num-sig b d o surj) env )
toℕ-term-homo (var x) env = lookup-map toℕ env x
toℕ-term-homo {b} {d} {o} {surj} (s ∔ t) env =
    begin
        ⟦ s ∔ t ⟧Term ℕ-sig (map toℕ env)
    ≡⟨ cong₂ _+_ (toℕ-term-homo {surj = surj} s env) (toℕ-term-homo {surj = surj} t env) ⟩
        toℕ (⟦ s ⟧Term _ env) + toℕ (⟦ t ⟧Term _ env)
    ≡⟨ sym (toℕ-⊹-homo (⟦ s ⟧Term _ env) (⟦ t ⟧Term _ env)) ⟩
        toℕ (⟦ s ∔ t ⟧Term (Num-sig b d o surj) env)
    ∎

mutual
    toℕ-pred-ℕ⇒Num : ∀ {b d o}
        → {surj : True (Surjective? b d o)}
        → ∀ {n}
        → (p : Pred n)
        → (env : Vec (Num b d o) n)
        → ⟦ p ⟧ ℕ-sig (map toℕ env)
        → ⟦ p ⟧ (Num-sig b d o surj) env
    -- toℕ-pred-ℕ⇒Num (p ≣ q) env ⟦p≡q⟧ℕ = {!   !}
    toℕ-pred-ℕ⇒Num {b} {d} {o} {surj} (p ≣ q) env a =
        -- a : ⟦ p ⟧Term ℕ-sig (ℕ-env) ≡ ⟦ q ⟧Term ℕ-sig (ℕ-env)

        let p' = ⟦ p ⟧Term {! Num-sig b d o surj  !} {!   !} {!   !}
            temp = toℕ-injective p' {!   !} a
        in
        {! toℕ-injective  !}
    toℕ-pred-ℕ⇒Num (p ⇒ q) env a = {!   !}
    toℕ-pred-ℕ⇒Num (All p) env a = {!   !}

    toℕ-pred-Num→ℕ : ∀ {b d o}
        → {surj : True (Surjective? b d o)}
        → ∀ {n}
        → (p : Pred n)
        → (env : Vec (Num b d o) n)
        → ⟦ p ⟧ (Num-sig b d o surj) env
        → ⟦ p ⟧ ℕ-sig (map toℕ env)
    toℕ-pred-Num→ℕ (p ≣ q) env a = {!   !}
    toℕ-pred-Num→ℕ (p ⇒ q) env a = {!   !}
    toℕ-pred-Num→ℕ (All p) env a = {!   !}


-- begin
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ∎

--
-- toℕ-term-homo : ∀ {b n}
--     → (t : Term n)
--     → (env : Vec (BijN b) n)
--     → ⟦ t ⟧Term ℕ-sig (map toℕ env) ≡ toℕ (⟦ t ⟧Term (BijN-sig b) env)
-- toℕ-term-homo     (var i)   env = ?
-- toℕ-term-homo {b} (t₁ ∔ t₂) env = ?
