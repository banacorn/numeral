module RandomAccessList.Redundant where

open import RandomAccessList.Redundant.Core
open import RandomAccessList.Redundant.Core.Properties
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
import BuildingBlock.BinaryLeafTree as BLT

-- open import Data.Fin
open import Data.Num.Nat
open import Data.Num.Redundant
open import Data.Num.Redundant.Properties
open import Data.Nat renaming (_<_ to _<ℕ_)
open import Data.Nat.DivMod
open import Data.Nat.Etc
open import Data.Product
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; subst; inspect)

--------------------------------------------------------------------------------
--  Operations
--------------------------------------------------------------------------------

consₙ : ∀ {n A} → BinaryLeafTree A n → 0-2-RAL A n → 0-2-RAL A n
consₙ a []            = a 1∷ []
consₙ a (      0∷ xs) = a 1∷ xs
consₙ a (x     1∷ xs) = a , x 2∷ xs
consₙ a (x , y 2∷ xs) = a 1∷ consₙ (Node x y) xs

cons : ∀ {A} → A → 0-2-RAL A 0 → 0-2-RAL A 0
cons a xs = consₙ (Leaf a) xs

headₙ :  ∀ {n A} → (xs : 0-2-RAL A n) → ⟦ xs ⟧ₙ ≉ zero ∷ [] → BinaryLeafTree A n
headₙ []            p = contradiction (eq refl) p
headₙ (      0∷ xs) p = proj₁ (BLT.split (headₙ xs (contraposition (>>-zero ⟦ xs ⟧ₙ) p)))
headₙ (x     1∷ xs) p = x
headₙ (x , y 2∷ xs) p = x

head : ∀ {A} → (xs : 0-2-RAL A 0) → ⟦ xs ⟧ ≉ zero ∷ [] → A
head xs p = BLT.head (headₙ xs p)

tailₙ : ∀ {n A} → (xs : 0-2-RAL A n) → ⟦ xs ⟧ₙ ≉ zero ∷ [] → 0-2-RAL A n
tailₙ []            p = contradiction (eq refl) p
tailₙ (      0∷ xs) p = proj₂ (BLT.split (headₙ xs (contraposition (>>-zero ⟦ xs ⟧ₙ) p))) 1∷ tailₙ xs (contraposition (>>-zero ⟦ xs ⟧ₙ) p)
tailₙ (x     1∷ xs) p = 0∷ xs
tailₙ (x , y 2∷ xs) p = y 1∷ xs

tail : ∀ {A} → (xs : 0-2-RAL A 0) → ⟦ xs ⟧ ≉ zero ∷ [] → 0-2-RAL A 0
tail xs p = tailₙ xs p

--------------------------------------------------------------------------------
--  Searching
--------------------------------------------------------------------------------

data Finite : Redundant → Set where
    finite  : ∀ {bound}                         -- # of elements
            → (a : Redundant)                   -- inhabitant
            → {a<bound : a < bound}             
            → Finite bound

elemAt : ∀ {n A} → (xs : 0-2-RAL A n) → Finite ⟦ xs ⟧ → A
elemAt {n} {A} [] (finite a {a<[]}) = contradiction a<[] {!   !}
-- elemAt {n} {A} [] (finite a {a<b}) = contradiction a<b (contraposition (map-≤ refl (to≡ (<<<-zero 0 ⟦ [] {A} {n} ⟧ {⟦[]⟧≈zero∷[] ([] {A} {n}) {refl}}))) (λ ()))
elemAt (0∷ xs) i = elemAt xs {!   !}
elemAt (x     1∷ xs) i = {!   !}
elemAt (x , y 2∷ xs) i = {!   !}









{-
-- data Occurrence : Set where
--    here : ∀ {a n} → a * Fin (2 ^ n) → Occurrence
--    there : Occurrence

transportFin : ∀ {a b} → a ≡ b → Fin a → Fin b
transportFin refl i = i



elemAt : ∀ {n A} → (xs : 0-2-RAL A n) → Fin ⟦ xs ⟧ → A
elemAt {zero} [] ()
elemAt {suc n} {A} []    i = elemAt {n} ([] {A} {n}) (transportFin (⟦[]⟧≡⟦[]⟧ {m = suc n} {n = n} {A = A}) i)
elemAt     (      0∷ xs) i = elemAt xs (transportFin (⟦0∷xs⟧≡⟦xs⟧ xs) i)
elemAt {n} (x     1∷ xs) i with (1 * 2 ^ n) ≤? toℕ i
elemAt     (x     1∷ xs) i | yes p rewrite splitIndex x xs = elemAt xs (reduce≥ i p)
elemAt {n} (x     1∷ xs) i | no ¬p with toℕ i divMod (2 ^ n)
elemAt (x 1∷ xs) i | no ¬p | result quotient remainder property = BLT.elemAt x remainder
elemAt {n} (x , y 2∷ xs) i with (2 * 2 ^ n) ≤? toℕ i
elemAt     (x , y 2∷ xs) i | yes p rewrite splitIndex2 x y xs = elemAt xs (reduce≥ i p)
elemAt {n} (x , y 2∷ xs) i | no ¬p with toℕ i divMod (2 ^ n)
elemAt (x , y 2∷ xs) i | no ¬p | result zero remainder property = BLT.elemAt x remainder
elemAt (x , y 2∷ xs) i | no ¬p | result (suc quotient) remainder property = BLT.elemAt y remainder
-}
