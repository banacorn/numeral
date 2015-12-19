module W where

open import Function using (_∘_)
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

data W (S : Set) (P : S → Set) : Set where
    sup : (s : S) → (f : P s → W S P) → W S P




-- data ℕ : Set where
--     zero : ℕ             _^0
--     succ : ℕ → ℕ        ∣ℕ∣

ℕ : Set
ℕ = W Bool f
    where   f : Bool → Set
            f true = ⊤
            f false = ⊥

zero : ℕ
zero = sup false ⊥-elim

succ : ℕ → ℕ
succ n = sup true (λ _ → n)

_+_ : ℕ → ℕ → ℕ
(sup true f) + y = sup true (λ _ → f tt + y)
(sup false f) + y = y

-- data Tree : Set where
--     leaf : Tree                   _^0
--     node : Tree → Tree → Tree    |ℕ| x |ℕ|

Tree : Set
Tree = W Bool λ { true → Bool ; false → ⊥ }

leaf : Tree
leaf = sup false ⊥-elim       -- _^0

node : Tree → Tree → Tree
node l r = sup true λ { true → l      -- ∣Tree∣^2
                     ; false → r }



data LW (S : Set) (LP : S → Set × Set) : Set where
     lsup : (s : Σ S (proj₁ ∘ LP)) → (proj₂ (LP (proj₁ s)) → LW S LP) → LW S LP

List : (X : Set) → Set
List X = LW Bool (λ { true → X , ⊤ ; false → ⊤ , ⊥ })

nil : {X : Set} → List X
nil = lsup (false , tt) ⊥-elim

cons : {X : Set} → (x : X) → List X → List X
cons {X} x xs = lsup (true , x) λ _ → xs



-- induction principle on W-types
indW : (S : Set)
     → (P : S → Set)
     → (C : W S P → Set)    --  property
     → (c : (s : S)                     -- given a shape
          → (f : P s → W S P)           -- and a bunch of kids
          → (h : (p : P s) → C (f p))   -- if C holds for all kids
          → C (sup s f))                -- C holds for (sup s f)
     → (x : W S P)
     → C x
indW S P C step (sup s f) = step s f (λ p → indW S P C step (f p))

-- indℕ : (C : ℕ → Set) → C zero → ((n : ℕ) → C n → C (succ n)) → (x : ℕ) → C x
-- indℕ C base step (sup true f) = step (f tt) (indℕ C base step (f tt))
-- indℕ C base step (sup false f) = {! base  !}
