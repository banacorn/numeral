module Data.Num.Bijection where

open import Data.Num.Core
open import Data.Num.Surjection
open import Data.Num.Injection

open import Data.Nat
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import Function.Bijection
open Bijective

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

data BijectionView : ℕ → ℕ → ℕ → Set where
    Bij     : ∀ {b d o} → SurjCond b d o → InjCond b d o → BijectionView b d o
    NonSurj : ∀ {b d o} → NonSurjCond b d o              → BijectionView b d o
    NonInj  : ∀ {b d o} → NonInjCond b d o               → BijectionView b d o

bijectionView : (b d o : ℕ) → BijectionView b d o
bijectionView b d o with surjectionView b d o | injectionView b d o
bijectionView b d o | Surj c₁    | Inj c₂    = Bij c₁ c₂
bijectionView b d o | Surj _     | NonInj c₁ = NonInj c₁
bijectionView b d o | NonSurj c₁ | _         = NonSurj c₁

IsBijective : ℕ → ℕ → ℕ → Set
IsBijective b d o with bijectionView b d o
IsBijective b d o | Bij _ _   = ⊤
IsBijective b d o | NonSurj _ = ⊥
IsBijective b d o | NonInj _  = ⊥

SurjCond∧InjCond⇒Bijective : ∀ {b} {d} {o} → SurjCond b d o → InjCond b d o → Bijective (Num⟶ℕ b d o)
SurjCond∧InjCond⇒Bijective surjCond injCond = record
    { injective = InjCond⇒Injective injCond
    ; surjective = SurjCond⇒Surjective surjCond
    }

NonSurjCond⇏Bijective : ∀ {b} {d} {o} → NonSurjCond b d o → ¬ (Bijective (Num⟶ℕ b d o))
NonSurjCond⇏Bijective reason claim = NonSurjCond⇏Surjective reason (surjective claim)

NonInjCond⇏Bijective : ∀ {b} {d} {o} → NonInjCond b d o → ¬ (Bijective (Num⟶ℕ b d o))
NonInjCond⇏Bijective reason claim = NonInjCond⇏Injective reason (injective claim)

Bijective? : ∀ b d o → Dec (Bijective (Num⟶ℕ b d o))
Bijective? b d o with bijectionView b d o
Bijective? b d o | Bij surjCond injCond = yes (record
    { injective = InjCond⇒Injective injCond
    ; surjective = SurjCond⇒Surjective surjCond
    })
Bijective? b d o | NonSurj reason       = no (NonSurjCond⇏Bijective reason)
Bijective? b d o | NonInj reason        = no (NonInjCond⇏Bijective reason)
