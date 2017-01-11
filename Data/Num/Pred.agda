module Data.Num.Pred where

open import Data.Num.Core
open import Data.Num
open import Data.Num.Properties
open import Data.Num.Continuous
-- open import Data.Num.Bijection

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Vec
open import Data.Product hiding (map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable using (True; fromWitness; toWitness)

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

-- infixl 6 _∔_
infixl 6 _∔_

data Term : ℕ → Set where
    var : ∀ {n} → Fin n → Term n
    _∔_ : ∀ {n} → Term n → Term n → Term n


data Predicate : ℕ → Set where
    -- equality
    _≋P_ : ∀ {n} → (t₁ : Term n) → (t₂ : Term n) → Predicate n
    -- implication
    _→P_ : ∀ {n} → (p₁ : Predicate n) → (p₂ : Predicate n) → Predicate n
    -- ∀, introduces new variable
    ∀P : ∀ {n} → (p : Predicate (suc n)) → Predicate n


record Signature : Set₁ where
    constructor sig
    field
        carrier : Set
        _⊕_ : carrier → carrier → carrier
        _≈_ : carrier → carrier → Set

open Signature

ℕ-sig : Signature
ℕ-sig = sig ℕ _+_ _≡_

Numeral-sig : (b d : ℕ) → True (Continuous? b d 0) → Signature
Numeral-sig b d cont = sig (Numeral b d 0) (_⊹_ {cont = cont}) _≋_

-- BijN-sig : ℕ → Signature
-- BijN-sig b = sig (BijN b) (_⊹_ {surj = fromWitness (BijN⇒Surjective b)}) _≡_
--

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

⟦_⟧P : ∀ {n}
    → Predicate n
    → (sig : Signature)
    → Env (carrier sig) n
    → Set
⟦ t₁ ≋P t₂ ⟧P (sig carrier _⊕_ _≈_) env
    = ⟦ t₁ ⟧T (sig carrier _⊕_ _≈_) env ≈ ⟦ t₂ ⟧T (sig carrier _⊕_ _≈_) env
⟦ p →P q   ⟧P signature env = ⟦ p ⟧P signature env → ⟦ q ⟧P signature env
⟦ ∀P pred  ⟧P signature env = ∀ x → ⟦ pred ⟧P signature (x ∷ env)

module Example-1 where
    ≋-trans : Predicate zero
    ≋-trans = let   x = var (# 0)
                    y = var (# 1)
                    z = var (# 2)
        in ∀P (∀P (∀P (((x ≋P y) →P (y ≋P z)) →P (x ≋P z))))

    ≋-trans-ℕ : Set
    ≋-trans-ℕ = ⟦ ≋-trans ⟧P ℕ-sig []

    ≋-trans-Numeral : (b d : ℕ) → True (Continuous? b d 0) → Set
    ≋-trans-Numeral b d prop = ⟦ ≋-trans ⟧P (Numeral-sig b d prop) []



-- lemma for env
lookup-map : ∀ {i j} → {A : Set i} {B : Set j}
           → (f : A → B) →
           ∀ {n} → (xs : Vec A n) (i : Fin n)
           → lookup i (map f xs) ≡ f (lookup i xs)
lookup-map f []       ()
lookup-map f (x ∷ xs) zero    = refl
lookup-map f (x ∷ xs) (suc i) = lookup-map f xs i




-- ------------------------------------------------------------------------
-- -- toℕ : preserving structures of terms and predicates
-- ------------------------------------------------------------------------


toℕ-term-homo : ∀ {b d n}
    → (cont : True (Continuous? b d 0))
    → (t : Term n)
    → (env : Vec (Numeral b d 0) n)
    → ⟦ t ⟧T ℕ-sig (map ⟦_⟧ env) ≡ ⟦ ⟦ t ⟧T (Numeral-sig b d cont) env ⟧
toℕ-term-homo     cont (var i)   env = lookup-map ⟦_⟧ env i
toℕ-term-homo {b} {d} cont (t₁ ∔ t₂) env
    rewrite toℕ-term-homo cont t₁ env | toℕ-term-homo cont t₂ env
    = sym (toℕ-⊹-homo cont (⟦ t₁ ⟧T (Numeral-sig b d cont) env) (⟦ t₂ ⟧T (Numeral-sig b d cont) env))

mutual
    toℕ-pred-ℕ⇒Numeral : ∀ {b d n}
        → (cont : True (Continuous? b (suc d) 0))
        → (pred : Predicate n)
        → (env : Vec (Numeral b (suc d) 0) n)
        → ⟦ pred ⟧P ℕ-sig (map ⟦_⟧ env)
        → ⟦ pred ⟧P (Numeral-sig b (suc d) cont) env
    toℕ-pred-ℕ⇒Numeral {b} {d} cont (t₁ ≋P t₂) env sem-ℕ =
        begin
            ⟦ ⟦ t₁ ⟧T (Numeral-sig b (suc d) cont) env ⟧
        ≡⟨ sym (toℕ-term-homo cont t₁ env) ⟩
            ⟦ t₁ ⟧T ℕ-sig (map ⟦_⟧ env)
        ≡⟨ sem-ℕ ⟩
            ⟦ t₂ ⟧T ℕ-sig (map ⟦_⟧ env)
        ≡⟨ toℕ-term-homo cont t₂ env ⟩
            ⟦ ⟦ t₂ ⟧T (Numeral-sig b (suc d) cont) env ⟧
        ∎
    toℕ-pred-ℕ⇒Numeral cont (p →P q) env sem-ℕ ⟦p⟧P-Numeral =
        toℕ-pred-ℕ⇒Numeral cont q env
            (sem-ℕ (toℕ-pred-Numeral⇒ℕ cont p env ⟦p⟧P-Numeral))
    toℕ-pred-ℕ⇒Numeral cont (∀P pred) env sem-ℕ x =
        toℕ-pred-ℕ⇒Numeral cont pred (x ∷ env) (sem-ℕ ⟦ x ⟧)

    toℕ-pred-Numeral⇒ℕ : ∀ {b d n}
        → (cont : True (Continuous? b (suc d) 0))
        → (pred : Predicate n)
        → (env : Vec (Numeral b (suc d) 0) n)
        → ⟦ pred ⟧P (Numeral-sig b (suc d) cont) env
        → ⟦ pred ⟧P ℕ-sig (map ⟦_⟧ env)
    toℕ-pred-Numeral⇒ℕ {b} {d} cont (t₁ ≋P t₂) env sem-Num =
        begin
            ⟦ t₁ ⟧T ℕ-sig (map ⟦_⟧ env)
        ≡⟨ toℕ-term-homo cont t₁ env ⟩
            ⟦ ⟦ t₁ ⟧T (Numeral-sig b (suc d) cont) env ⟧
        ≡⟨ sem-Num ⟩
            ⟦ ⟦ t₂ ⟧T (Numeral-sig b (suc d) cont) env ⟧
        ≡⟨ sym (toℕ-term-homo cont t₂ env) ⟩
            ⟦ t₂ ⟧T ℕ-sig (map ⟦_⟧ env)
        ∎
    toℕ-pred-Numeral⇒ℕ cont (p →P q) env sem-Num ⟦p⟧P
        = toℕ-pred-Numeral⇒ℕ cont q env
            (sem-Num
                (toℕ-pred-ℕ⇒Numeral cont p env ⟦p⟧P))
    toℕ-pred-Numeral⇒ℕ {b} {d} cont (∀P pred) env sem-Num n with n ≟ ⟦ fromℕ {cont = cont} n z≤n ⟧
    toℕ-pred-Numeral⇒ℕ {b} {d} cont (∀P pred) env sem-Num n | yes eq
        rewrite eq
        = toℕ-pred-Numeral⇒ℕ cont pred (fromℕ {cont = cont} n _ ∷ env) (sem-Num (fromℕ {cont = cont} n _))
    toℕ-pred-Numeral⇒ℕ {b} {d} cont (∀P pred) env sem-Num n | no ¬eq
        = contradiction (sym (fromℕ-toℕ cont n _)) ¬eq

module Example-2 where

    +-comm-Predicate : Predicate 0
    +-comm-Predicate = ∀P (∀P ((var (# 1) ∔ var (# 0)) ≋P (var (# 0) ∔ var (# 1))))

    +-comm-ℕ : ∀ a b → a + b ≡ b + a
    +-comm-ℕ = +-comm

    +-comm-Num : ∀ {b d}
        → {cont : True (Continuous? b (suc d) 0)}
        → (xs ys : Numeral b (suc d) 0)
        → (_⊹_ {cont = cont} xs ys) ≋ (_⊹_ {cont = cont} ys xs)
    +-comm-Num {cont = cont} = toℕ-pred-ℕ⇒Numeral cont +-comm-Predicate [] +-comm-ℕ
--
-- mutual
--     toℕ-pred-ℕ⇒Bij : ∀ {b n}
--                 → (pred : Predicate n)
--                 → (env  : Vec (Bij (suc b)) n)
--                 → ⟦ pred ⟧ ℕ-sig            (map toℕ env)
--                 → ⟦ pred ⟧ (BijN-sig (suc b)) env
--     toℕ-pred-ℕ⇒Bij {b} (t₁ ≋ t₂) env ⟦t₁≈t₂⟧ℕ
--         rewrite toℕ-term-homo t₁ env | toℕ-term-homo t₂ env -- ⟦ t₁ ⟧T ℕ-sig (map toℕ env) ≡ toℕ (⟦ t₁ ⟧T (Bij-sig (suc b)) env)
--         = toℕ-injective (⟦ t₁ ⟧T (BijN-sig (suc b)) env) (⟦ t₂ ⟧T (BijN-sig (suc b)) env) ⟦t₁≈t₂⟧ℕ
--     toℕ-pred-ℕ⇒Bij (p ⇒ q)   env ⟦p→q⟧ℕ ⟦p⟧B = toℕ-pred-ℕ⇒Bij q env (⟦p→q⟧ℕ (toℕ-pred-Bij⇒ℕ p env ⟦p⟧B))
--     toℕ-pred-ℕ⇒Bij (All p)   env ⟦λx→p⟧ℕ x = toℕ-pred-ℕ⇒Bij p (x ∷ env) (⟦λx→p⟧ℕ (toℕ x))
--
--     toℕ-pred-Bij⇒ℕ : ∀ {b n}
--                 → (pred : Predicate n)
--                 → (env  : Vec (Bij (suc b)) n)
--                 → ⟦ pred ⟧ (BijN-sig (suc b)) env
--                 → ⟦ pred ⟧ ℕ-sig             (map toℕ env)
--     toℕ-pred-Bij⇒ℕ (t₁ ≋ t₂) env ⟦t₁≈t₂⟧B
--         rewrite toℕ-term-homo t₁ env | toℕ-term-homo t₂ env
--         = cong toℕ ⟦t₁≈t₂⟧B
--     toℕ-pred-Bij⇒ℕ (p ⇒ q) env ⟦p→q⟧B ⟦p⟧ℕ = toℕ-pred-Bij⇒ℕ q env (⟦p→q⟧B (toℕ-pred-ℕ⇒Bij p env ⟦p⟧ℕ))
--     toℕ-pred-Bij⇒ℕ {b} (All p) env ⟦λx→p⟧B x
--         rewrite (sym (toℕ-fromℕ b x)) -- rewritting "x" to "toℕ (fromℕ x)"
--         = toℕ-pred-Bij⇒ℕ p (fromℕ x ∷ env) (⟦λx→p⟧B (fromℕ x))


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
