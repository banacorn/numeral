module Data.Num.Sandbox.WF where

open import Data.Nat
-- open import Relation.Binary
--
-- open DecTotalOrder decTotalOrder
--   using (trans)
--
-- data Acc (n : ℕ) : Set where
--     acc : (∀ m → m < n → Acc m) → Acc n
--
-- go0 : (m : ℕ) → m < 0 → Acc m
-- go0 m ()
--
-- <-wf : ∀ n → Acc n
-- <-wf n = acc (go n)
--     where   go : (n m : ℕ) → m < n → Acc m
--             go zero m ()
--             go (suc n₁) zero m<n = acc (λ _ → λ ())
--             go (suc n₁) (suc m) (s≤s m<n₁) = acc (λ m₁ m₁<m+1 → go n₁ m₁ (trans m₁<m+1 m<n₁))

pp : ℕ → ℕ
pp zero = zero
pp (suc zero) = zero
pp (suc (suc n)) = n
--
-- f : ℕ → ℕ
-- f n = go n (<-wf n)
--     where
--         go : ∀ n → Acc n → ℕ
--         go zero    _ = zero
--         go (suc n) (acc a) = go (pp (suc n)) (a (pp (suc n)) {!   !})

open import Induction.Nat

half : ℕ → ℕ
half = <-rec _ go
    where   go : (x : ℕ) → ((y : ℕ) → suc y ≤′ x → ℕ) → ℕ
            go zero acc = zero
            go (suc zero) acc = zero
            go (suc (suc n)) acc = suc (acc n (≤′-step ≤′-refl))
