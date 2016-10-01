module W where

open import Function using (_∘_)
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

data W (S : Set) (P : S → Set) : Set where
    max : (s : S) → (f : P s → W S P) → W S P

-- data ℕ : Set where
--     zero : ℕ             _^0
--     succ : ℕ → ℕ        ∣ℕ∣

ℕ : Set
ℕ = W Bool f
    where   f : Bool → Set
            f true = ⊤ -- 1
            f false = ⊥ -- 0

zero : ℕ
zero = max false ⊥-elim

succ : ℕ → ℕ
succ n = max true (λ _ → n)

_+_ : ℕ → ℕ → ℕ
(max true f) + y = max true (λ _ → f tt + y)
(max false f) + y = y

-- data Tree : Set where
--     leaf : Tree                   _^0
--     node : Tree → Tree → Tree    |ℕ| x |ℕ|

Tree : Set
Tree = W Bool λ { true → Bool ; false → ⊥ }

leaf : Tree
leaf = max false ⊥-elim       -- _^0

node : Tree → Tree → Tree
node l r = max true λ { true → l      -- ∣Tree∣^2
                     ; false → r }



data LW (S : Set) (LP : S → Set × Set) : Set where
     lmax : (s : Σ S (proj₁ ∘ LP)) → (proj₂ (LP (proj₁ s)) → LW S LP) → LW S LP

List : (X : Set) → Set
List X = LW Bool (λ { true → X , ⊤      -- cons
                    ; false → ⊤ , ⊥ })  -- nil

nil : {X : Set} → List X
nil = lmax (false , tt) ⊥-elim

cons : {X : Set} → (x : X) → List X → List X
cons {X} x xs = lmax (true , x) λ _ → xs



-- induction principle on W-types
indW : (S : Set)
     → (P : S → Set)
     → (C : W S P → Set)    --  property
     → (c : (s : S)                     -- given a shape
          → (f : P s → W S P)           -- and a bunch of kids
          → (h : (p : P s) → C (f p))   -- if C holds for all kids
          → C (max s f))                -- C holds for (max s f)
     → (x : W S P)
     → C x
indW S P C step (max s f) = step s f (λ p → {!   !} S P C step (f p))

indℕ : (C : ℕ → Set) → C zero → ((n : ℕ) → C n → C (succ n)) → (x : ℕ) → C x
indℕ C base step (max true f) = step (f tt) (indℕ C base step (f tt))
indℕ C base step (max false f) = {! base  !}
