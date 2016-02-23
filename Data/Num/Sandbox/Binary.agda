module Data.Num.Binary where


-- open import Data.Product using (_×_; Σ; _,_)
open import Data.List
open import Data.Unit
open import Data.Empty
-- open import Data.Nat renaming (_+_ to _⊹_)
--
-- data Bin : Set where
--     [] : Bin
--     0- : Bin → Bin
--     1- : Bin → Bin
--
-- carry : Bin → Bin
-- carry [] = 1- []
-- carry (0- xs) = 1- xs
-- carry (1- xs) = 0- (carry xs)
--
-- _+_ : Bin → Bin → Bin
-- [] + ys = ys
-- xs + [] = xs
-- 0- xs + 0- ys = 0- (xs + ys)
-- 0- xs + 1- ys = 1- (xs + ys)
-- 1- xs + 0- ys = 1- (xs + ys)
-- 1- xs + 1- ys = 0- (carry (xs + ys))
--

-- data Desc : Set₁ where
--     arg : (A : Set)             -- a bag of tags to choose constructors with
--         → (A → Desc)            -- given a tag, return the description of the constructor it corresponds to
--         → Desc
--     rec : Desc → Desc           -- recursive subnode
--     ret : Desc                  -- stop
--
-- -- the "decoder", "interpreter"
-- -- ⟦_⟧ : Desc → Set → Set
-- -- ⟦ arg A D ⟧ R = Σ A (λ a → ⟦ D a ⟧ R)
-- -- ⟦ rec D   ⟧ R = R × ⟦ D ⟧ R
-- -- ⟦ ret     ⟧ R = ⊤

-- data BinF : Set where
--     arg : (ℕ → BinF) → BinF
--     rec : BinF → BinF
--     ret : BinF
--
-- ⟦_⟧ : BinF → Set → Set
-- ⟦_⟧ (arg F) X = Σ ℕ (λ n → ⟦ F n ⟧ X)
-- ⟦_⟧ (rec F) X = X × ⟦ F ⟧ X
-- ⟦_⟧ ret X = ⊤
--
-- data μ (F : BinF) : Set where
--     ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F
--
-- Bin : Set
-- Bin = μ (arg {! λ   !})

--
-- data Digit : Set where
--     [0] : Digit
--     [1] : Digit
--
-- Binary : Set
-- Binary = List Digit
--
-- _⊕_ : Digit → Digit → Digit
-- [0] ⊕ [0] = [0]
-- [0] ⊕ [1] = [1]
-- [1] ⊕ [0] = [1]
-- [1] ⊕ [1] = [0]
--
-- _⊚_ : Digit → Digit → Digit
-- [1] ⊚ [1] = [1]
-- _   ⊚ _   = [0]
--
-- carry : Digit → Binary → Binary
-- carry [0] ys = ys
-- carry [1] [] = [1] ∷ []
-- carry [1] ([0] ∷ ys) = [1] ∷ ys
-- carry [1] ([1] ∷ ys) = [0] ∷ carry [1] ys
--
-- _+_ : Binary → Binary → Binary
-- [] + ys = ys
-- xs + [] = xs
-- (x ∷ xs) + (y ∷ ys) = x ⊕ y ∷ carry (x ⊚ y) (xs + ys)
--
-- _≈_ : Binary → Binary → Set
-- [] ≈ [] = ⊤
-- [] ≈ (y ∷ ys) = ⊥
-- (x ∷ xs) ≈ [] = ⊥
-- ([0] ∷ xs) ≈ ([0] ∷ ys) = xs ≈ ys
-- ([0] ∷ xs) ≈ ([1] ∷ ys) = ⊥
-- ([1] ∷ xs) ≈ ([0] ∷ ys) = ⊥
-- ([1] ∷ xs) ≈ ([1] ∷ ys) = xs ≈ ys

data Bin : Set where
    ∙ : Bin
    [0]_ : Bin → Bin
    [1]_ : Bin → Bin

two : Bin
two = [1] [0] ∙

1+ : Bin → Bin
1+ ∙ = [1] ∙
1+ ([0] x) = [1] x
1+ ([1] x) = [0] 1+ x

_+_ : Bin → Bin → Bin
∙ + ys = ys
xs + ∙ = xs
([0] xs) + ([0] ys) = [0] (xs + ys)
([0] xs) + ([1] ys) = [1] (xs + ys)
([1] xs) + ([0] ys) = [1] (xs + ys)
([1] xs) + ([1] ys) = [0] (1+ (xs + ys))
