module Sandbox.PrimitiveRecursion where

open import Data.Nat
open import Data.Fin using (Fin)
open import Data.Vec

data PR : ℕ → Set where
    -- Constant function: The 0-ary constant function 0 is primitive recursive.
    K : PR 0

    -- Successor function: The 1-ary successor function S, which returns the
    -- successor of its argument (see Peano postulates), is primitive recursive.
    -- That is, S(k) = k + 1.
    S : PR 1

    -- Projection function: For every n≥1 and each i with 1≤i≤n, the n-ary
    -- projection function Pᵢⁿ, which returns its i-th argument, is primitive
    -- recursive.
    Proj : ∀ {n} → (i : Fin n) → PR n

    -- Composition: Given f, a m-ary primitive recursive function, and m n-ary
    -- primitive recursive functions g1,...,gm, the composition of f with
    -- g1,...,gk, is primitive recursive
    --  f(
    --      g₁(x₁, x₂, ..., xₙ)
    --      g₂(x₁, x₂, ..., xₙ)
    --      ...
    --      gₘ(x₁, x₂, ..., xₙ)
    --  )
    Comp : ∀ {m n} → (f : PR m) → Vec (PR n) m → PR n
    -- Primitive recursion: Given f, a m-ary primitive recursive function,
    -- and g, a (m+2)-ary primitive recursive function, the (m+1)-ary function
    -- h is defined as the primitive recursion of f and g, i.e. the function h
    -- is primitive recursive when
    --  h(0   , x₁, x₂, .. xₘ) = f(x₁, x₂, .. xₘ)
    --  h(S(n), x₁, x₂, .. xₘ) = g(n, h(n, x₁, x₂, .. xₘ), x₁, x₂, .. xₘ)
    Rec : ∀ {n} → (f : PR {!   !}) (g : PR (suc (suc n))) → PR (suc n)


mutual
    ⟦_⟧_ : ∀ {a} → PR a → Vec ℕ a → ℕ
    ⟦ K         ⟧ args           = zero
    ⟦ S         ⟧ args           = suc zero
    ⟦ Proj i    ⟧ args           = lookup i args
    ⟦ Comp f gs ⟧ args           = ⟦ f ⟧ (⟦ gs ⟧* args)
    ⟦ Rec  f g  ⟧ (zero  ∷ args) = ⟦ f ⟧ args
    ⟦ Rec  f g  ⟧ (suc x ∷ args) = ⟦ g ⟧ (x ∷ (⟦ f ⟧ args) ∷ args)

    ⟦_⟧* : {m n : ℕ} (gs : Vec (PR n) m) → Vec ℕ n → Vec ℕ m
    ⟦ []     ⟧* args = []
    ⟦ g ∷ gs ⟧* args = (⟦ g ⟧ args) ∷ ⟦ gs ⟧* args
