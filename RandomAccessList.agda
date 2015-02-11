module RandomAccessList where

open import RandomAccessList.Core
open import RandomAccessList.Properties
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
import BuildingBlock.BinaryLeafTree as BLT

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; fromℕ≤; reduce≥; toℕ)
import      Data.Fin as Fin
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Nat.Exp
open import Data.Product as Prod
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------
-- predicates

null : ∀ {A n} → RandomAccessList A n → Set
null []        = ⊤
null (  0∷ xs) = null xs
null (x 1∷ xs) = ⊥

null? : ∀ {A n} → (xs : RandomAccessList A n) → Dec (null xs)
null? []        = yes tt
null? (  0∷ xs) = null? xs
null? (x 1∷ xs) = no (λ z → z)

--------------------------------------------------------------------------------
-- Operations

-- numerical: +1
-- container: insertion
incr : ∀ {A n} → BinaryLeafTree A n → RandomAccessList A n → RandomAccessList A n
incr a []        = a 1∷ []
incr a (  0∷ xs) = a 1∷ xs
incr a (x 1∷ xs) =   0∷ (incr (Node a x) xs)

-- numerical: +
-- container: merge
_++_ : ∀ {A n} → RandomAccessList A n → RandomAccessList A n → RandomAccessList A n
[]        ++ ys        =      ys
(  0∷ xs) ++ []        =   0∷ xs
(  0∷ xs) ++ (  0∷ ys) =   0∷ (xs ++ ys)
(  0∷ xs) ++ (x 1∷ ys) = x 1∷ (xs ++ ys)
(x 1∷ xs) ++ []        = x 1∷ xs
(x 1∷ xs) ++ (  0∷ ys) = x 1∷ (xs ++ ys)
(x 1∷ xs) ++ (y 1∷ ys) =   0∷ (incr (Node x y) (xs ++ ys))

-- borrow from the first non-zero digit, and splits it like so (1:xs)
-- numerical: borrow
borrow : ∀ {A n}
        → (xs : RandomAccessList A n)
        → False (null? xs)
        → RandomAccessList A n × RandomAccessList A n
borrow []        ()
borrow (  0∷ xs) p  with null? xs
borrow (  0∷ xs) () | yes q
borrow (  0∷ xs) tt | no ¬q = Prod.map 0∷_ 0∷_ (borrow xs (fromWitnessFalse ¬q))
borrow (x 1∷ xs) p  = x 1∷ [] , 0∷ xs

-- numerical: -1
-- container: deletion
decr : ∀ {A n} → (xs : RandomAccessList A n) → False (null? xs) → RandomAccessList A n
decr []        ()
decr (  0∷ xs) p  with null? xs
decr (  0∷ xs) () | yes q
decr (  0∷ xs) tt | no ¬q = 0∷ (proj₂ (borrow xs (fromWitnessFalse ¬q)))
decr (x 1∷ xs) p = 0∷ xs

--------------------------------------------------------------------------------
-- Searching

transportFin : ∀ {a b} → a ≡ b → Fin a → Fin b
transportFin refl i = i

splitIndex : ∀ {n A} → (x : BinaryLeafTree A n) → (xs : RandomAccessList A (suc n)) → ⟦ x 1∷ xs ⟧ ≡ (2 ^ n) + ⟦ 0∷ xs ⟧
splitIndex {n} x xs =
    begin
        ⟦ x 1∷ xs ⟧
    ≡⟨ ⟦xs⟧≡2ⁿ*⟦xs⟧ₙ (x 1∷ xs) ⟩
        2 ^ n * suc (2 * ⟦ xs ⟧ₙ)
    ≡⟨ +-*-suc (2 ^ n) (2 * ⟦ xs ⟧ₙ) ⟩
        2 ^ n + 2 ^ n * (2 * ⟦ xs ⟧ₙ)
    ≡⟨ cong (_+_ (2 ^ n)) (sym (⟦xs⟧≡2ⁿ*⟦xs⟧ₙ (0∷ xs))) ⟩
        (2 ^ n) + ⟦ 0∷ xs ⟧
    ∎

elemAt : ∀ {n A} → (xs : RandomAccessList A n) → Fin ⟦ xs ⟧ → A
elemAt {zero}  (     []) ()
elemAt {suc n} (     []) i  = elemAt {n} ([] {n = n}) (transportFin (⟦[]⟧≡⟦[]⟧ {n}) i)
elemAt         (  0∷ xs) i  with ⟦ 0∷ xs ⟧ | inspect ⟦_⟧ (0∷ xs)
elemAt         (  0∷ xs) () | zero  | _
elemAt         (  0∷ xs) i  | suc z | PropEq.[ eq ] = elemAt xs (transportFin (sym eq) i)
elemAt {n}     (x 1∷ xs) i  with (2 ^ n) ≤? toℕ i
elemAt {n}     (x 1∷ xs) i  | yes p rewrite splitIndex x xs = elemAt xs (reduce≥ i p)
elemAt         (x 1∷ xs) i  | no ¬p = BLT.elemAt x (fromℕ≤ (BLT.¬a≤b⇒b<a ¬p))
