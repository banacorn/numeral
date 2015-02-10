module BuildingBlock where

open import Data.Nat


_^_ : ℕ → ℕ → ℕ
a ^ zero  = 1
a ^ suc b = a * (a ^ b)

--------------------------------------------------------------------------------
-- Binomial Tree

-- NodeList C n : list of C indexed from 0 to n
data NodeList (C : ℕ → Set) : ℕ → Set where
    Nil : C 0 → NodeList C 0
    Cons : ∀ {n} → C (suc n) → NodeList C n → NodeList C (suc n)

data BinomialTree (A : Set) : ℕ → Set where
    Leaf : A → BinomialTree A 0
    Node : ∀ {n} → A → NodeList (BinomialTree A) n → BinomialTree A (suc n)

-- examples
private
    ein : BinomialTree ℕ 0
    ein = Leaf 0

    zwei : BinomialTree ℕ 1
    zwei = Node 1
            (Nil (Leaf 0))

    fier' : BinomialTree ℕ 2
    fier' = Node 0
            (Cons (Node 1
                (Nil (Leaf 2)))
            (Nil (Leaf 3)))

--------------------------------------------------------------------------------
-- Pennants

data CompleteBinaryTree (A : Set) : ℕ → Set where
    Leaf : A → CompleteBinaryTree A 0
    Node : ∀ {n}  → A
                → CompleteBinaryTree A n
                → CompleteBinaryTree A n
                → CompleteBinaryTree A (suc n)

data Pennants (A : Set) : ℕ → Set where
    Leaf : A → Pennants A 0
    Node : ∀ {n}  → A
                → CompleteBinaryTree A n
                → Pennants A n

-- examples
private
    zweiP : Pennants ℕ 2
    zweiP = Node 0 (Node 1
                    (Node 2
                        (Leaf 3)
                        (Leaf 4))
                    (Node 5
                        (Leaf 6) (Leaf 7)))
