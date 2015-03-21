module Misc.PosBinary where  -- Positive Binary Numbers

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)

open import Induction.WellFounded
open import Induction.Nat using (<-well-founded)

data Bin+ : Set where
  [] : Bin+
  1∷_ : Bin+ → Bin+
  2∷_ : Bin+ → Bin+

decimal : Bin+ → ℕ
decimal [] = 0
decimal (1∷ xs) = 1 + 2 * decimal xs
decimal (2∷ xs) = 2 + 2 * decimal xs

-- A even/odd view. Surprised that we don't have it in StdLib

data Div2 : ℕ → Set where
  even : ∀ n → Div2 (2 * n)
  odd  : ∀ n → Div2 (1 + 2 * n)

open import Data.Nat.Properties.Simple using (+-suc)
  -- +-suc : ∀ m n → m + suc n ≡ suc (m + n)
open import Data.Nat.Properties using (m≤′m+n)
  -- m≤′m+n : ∀ m n → m ≤′ m + n

_div2 : ∀ n → Div2 n
zero div2 = even 0
suc n div2 with n div2
suc .(n + (n + 0)) div2       | even n = odd n
suc .(suc (n + (n + 0))) div2 | odd n
      rewrite sym (+-suc n (n + zero)) = even (1 + n)

bin+' : (n : ℕ) → Acc _<′_ n → Bin+
bin+' n _ with n div2
bin+' .0 _                              | even zero = []
bin+' .(suc (m + suc (m + 0))) (acc rs) | even (suc m) =
   2∷ bin+' m (rs m (m≤′m+n (suc m) _))
bin+' .(suc (m + (m + 0)))     (acc rs) | odd m  =
   1∷ bin+' m (rs m (m≤′m+n (suc m) _))

bin+ : ℕ → Bin+
bin+ n = bin+' n (<-well-founded n)

{-  For reference.

bin' : (n : ℕ) → Acc _<′_ n → List ℕ
bin' n _ with n div2
bin' .0 (acc rs) | even 0 = []
bin' .(suc m + (suc m + 0)) (acc rs) | even (suc m) =
     0 ∷ bin' m (rs m (m≤′m+n (suc m) _))
bin' .(suc (m + (m + 0))) (acc rs)   | odd m =
     1 ∷ bin' m (rs m (m≤′m+n (suc m) _))

bin : ℕ → List ℕ
bin n = bin' n (<-well-founded n)
-}

lInv' : ∀ n → (ac : Acc _<′_ n) → decimal (bin+' n ac) ≡ n
lInv' n ac with n div2
lInv' .0 ac | even zero = refl
lInv' .(suc (m + suc (m + 0))) (acc rs) | even (suc m)
  rewrite lInv' m (rs m (m≤′m+n (suc m) (suc (m + zero))))
        | +-suc m (m + 0) = refl
lInv' .(suc (m + (m + 0))) (acc rs) | odd m
  rewrite lInv' m (rs m (m≤′m+n (suc m) (m + zero))) = refl

lInv : ∀ n → decimal (bin+ n) ≡ n
lInv n = lInv' n (<-well-founded n)
