module Data.Num.Bijection where

open import Data.Num.Core
open import Data.Num.Surjection

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra

open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)
open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)
open import Data.Product
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)


-- open import Function
-- open import Function.Injective hiding (_∘_)
-- open Injective
-- open import Function.Equality using (_⟶_; _⟨$⟩_)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)


record BijCond (b d o : ℕ) : Set where
    constructor bijCond
    field
        b≥1 : b ≥ 1
        b≡d : b ≡ d
        o≡1 : o ≡ 1

data NonBijCond : ℕ → ℕ → ℕ → Set where
    Base≡0      : ∀ {  d o}         → NonBijCond 0 d o
    Offset≢1    : ∀ {b d o} → o ≢ 1 → NonBijCond b d o
    Base≢#Digit : ∀ {b d o} → b ≢ d → NonBijCond b d o

data BijectionView : ℕ → ℕ → ℕ → Set where
    Bij    : ∀ {b d o} → BijCond b d o   → BijectionView b d o
    NonBij : ∀ {b d o} → NonBijCond b d o → BijectionView b d o

bijectionView : (b d o : ℕ) → BijectionView b d o
bijectionView 0       d o = NonBij Base≡0
bijectionView (suc b) d 0 = NonBij (Offset≢1 (λ ()))
bijectionView (suc b) d 1 with suc b ≟ d
bijectionView (suc b) d 1 | yes p = Bij (bijCond (s≤s z≤n) p refl)
bijectionView (suc b) d 1 | no ¬p = NonBij (Base≢#Digit ¬p)
bijectionView (suc b) d (suc (suc o)) = NonBij (Offset≢1 (λ ()))

IsBijective : ℕ → ℕ → ℕ → Set
IsBijective b d o with bijectionView b d o
IsBijective b d o | Bij x    = ⊤
IsBijective b d o | NonBij x = ⊥

BijCond⇒IsBij : ∀ {b d o} → BijCond b d o → IsBijective b d o
BijCond⇒IsBij {b} {d} {o} cond with bijectionView b d o
BijCond⇒IsBij _                     | Bij _                     = tt
BijCond⇒IsBij (bijCond ()  b≡d o≡1) | NonBij Base≡0
BijCond⇒IsBij (bijCond b≥1 b≡d o≡1) | NonBij (Offset≢1 o≢1)    = contradiction o≡1 o≢1
BijCond⇒IsBij (bijCond b≥1 b≡d o≡1) | NonBij (Base≢#Digit b≢d) = contradiction b≡d b≢d

NonBijCond⇏IsBij : ∀ {b d o} → NonBijCond b d o → ¬ IsBijective b d o
NonBijCond⇏IsBij {b} {d} {o} reason claim with bijectionView b d o
NonBijCond⇏IsBij Base≡0            claim | Bij (bijCond () b≡d o≡1)
NonBijCond⇏IsBij (Offset≢1 o≢1)    claim | Bij (bijCond b≥1 b≡d o≡1) = contradiction o≡1 o≢1
NonBijCond⇏IsBij (Base≢#Digit b≢d) claim | Bij (bijCond b≥1 b≡d o≡1) = contradiction b≡d b≢d
NonBijCond⇏IsBij _ () | NonBij _

IsBij⇒IsSurj : ∀ {b d} → IsBijective b d 1 → IsSurjective b d 1
IsBij⇒IsSurj {b} {d} condition with bijectionView b d 1 | surjectionView b d 1
IsBij⇒IsSurj condition | Bij _                      | Surj _ = tt
IsBij⇒IsSurj condition | Bij (bijCond ()  b≡d o≡1) | NonSurj Base≡0
IsBij⇒IsSurj condition | Bij (bijCond b≥1 b≡d o≡1) | NonSurj NoDigits = contradiction b≡d (>⇒≢ b≥1)
IsBij⇒IsSurj condition | Bij (bijCond b≥1 b≡d o≡1) | NonSurj (Offset≥2 (s≤s ()))
IsBij⇒IsSurj condition | Bij (bijCond b≥1 b≡d o≡1) | NonSurj (NotEnoughDigits d≥1 b≰d) = contradiction (reflexive b≡d) b≰d
IsBij⇒IsSurj condition | NonBij _                   | Surj _ = tt
IsBij⇒IsSurj ()        | NonBij _                   | NonSurj _
