module Data.Nat.Etc where

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Function
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; refl; cong; trans; sym)
open PropEq.≡-Reasoning

-- exponention
_^_ : ℕ → ℕ → ℕ
a ^ zero  = 1
a ^ suc b = a * (a ^ b)


--------------------------------------------------------------------------------
-- Properties

distrib-left-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
distrib-left-*-+ m n o =
        begin
            m * (n + o)
        ≡⟨ *-comm m (n + o) ⟩
            (n + o) * m
        ≡⟨ distribʳ-*-+ m n o ⟩
            n * m + o * m
        ≡⟨ cong (flip _+_ (o * m)) (*-comm n m) ⟩
            m * n + o * m
        ≡⟨ cong (_+_ (m * n)) (*-comm o m) ⟩
            m * n + m * o
        ∎
