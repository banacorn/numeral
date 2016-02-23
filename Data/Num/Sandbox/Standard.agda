module Data.Num.Standard where

open import Data.Nat using (ℕ; suc; zero; _≤?_)
open import Data.Fin using (Fin; fromℕ; #_)
open import Level using () renaming (suc to lsuc)
    -- renaming (zero to Fzero; suc to Fsuc; toℕ to F→N; fromℕ≤ to N→F)
open import Relation.Nullary.Decidable


infixr 2 [_]_

-- invariant: base ≥ 1
data Num : ℕ → Set where
    ∙ : ∀ {b} → Num (suc b)
    [_]_ : ∀ {b} → (n : ℕ) → {in-bound : True (n ≤? b)} → Num (suc b) → Num (suc b)

null : Num 2
null = [ 0 ] ∙

eins : Num 2
eins = [ 1 ] ∙

zwei : Num 3
zwei = [ 1 ] [ 2 ] ∙

carry : ∀ {b} → Num b → Num b
carry {zero} ()
carry {suc b} ∙ = [ {!   !} ] ∙
carry {suc b} ([ n ] xs) = {!   !}

_+_ : ∀ {b} → Num b → Num b → Num b
∙ + ys = ys
xs + ∙ = xs
([ x ] xs) + ([ y ] ys) = {!   !}
