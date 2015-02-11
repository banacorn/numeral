module RandomAccessList where

open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
import BuildingBlock.BinaryLeafTree as BLT

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat
open import Data.Nat.Exp
open import Data.Nat.Properties.Simple
import Data.Fin as Fin
open import Data.Product as Prod
open import Data.Product hiding (map)
open import Function
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------
--  data type

--  parameterized by the level of the least significant digit
data RandomAccessList (A : Set) : ℕ → Set where
    []   : ∀ {n} → RandomAccessList A n
    0∷_  : ∀ {n} → RandomAccessList A (suc n) → RandomAccessList A n
    _1∷_ : ∀ {n} → BinaryLeafTree A n → RandomAccessList A (suc n) → RandomAccessList A n

--------------------------------------------------------------------------------
-- examples
{-
private
    a : RandomAccessList ℕ 0
    a = Leaf zero 1∷ []
    b : RandomAccessList ℕ 1
    b = (Node (Leaf 0) (Leaf 1)) 1∷ []
    c : RandomAccessList ℕ 1
    c = 0∷ ((Node (Node (Leaf 0) (Leaf 1)) (Node (Leaf 2) (Leaf 3))) 1∷ [])
    d : RandomAccessList ℕ 1
    d = []
    d' : RandomAccessList ℕ 0
    d' = 0∷ d
    e : RandomAccessList ℕ 0
    e = []
-}
--------------------------------------------------------------------------------
-- to ℕ

⟦_⟧ₙ : ∀ {A n} → RandomAccessList A n → ℕ
⟦      [] ⟧ₙ = 0
⟦   0∷ xs ⟧ₙ =     2 * ⟦ xs ⟧ₙ
⟦ x 1∷ xs ⟧ₙ = 1 + 2 * ⟦ xs ⟧ₙ

normalize : ∀ {n A} → RandomAccessList A n → RandomAccessList A 0
normalize {zero} xs = xs
normalize {suc n} xs = normalize (0∷ xs)

⟦_⟧ : ∀ {A n} → RandomAccessList A n → ℕ
⟦_⟧ xs = ⟦ normalize xs ⟧ₙ

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
-- operations

-- numerical: +1
-- container: insertion
incr : ∀ {A n} → BinaryLeafTree A n → RandomAccessList A n → RandomAccessList A n
incr a []        = a 1∷ []
incr a (  0∷ xs) = a 1∷ xs
incr a (x 1∷ xs) =   0∷ (incr (Node a x) xs)

-- not needed for the moment
-- numerical: carry
carry : ∀ {A n} → BinaryLeafTree A n → BinaryLeafTree A n → BinaryLeafTree A (suc n)
carry x y = Node x y

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

shift : ∀ {A n} → RandomAccessList A n → RandomAccessList A (suc n)
shift []        = []
shift (  0∷ xs) = xs
shift (x 1∷ xs) = xs

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

private
    ⟦xs⟧≡2ⁿ*⟦xs⟧ₙ : ∀ {A n} → (xs : RandomAccessList A n)
                           → ⟦ xs ⟧ ≡ (2 ^ n) * ⟦ xs ⟧ₙ
    ⟦xs⟧≡2ⁿ*⟦xs⟧ₙ {n = zero } xs = sym (+-right-identity ⟦ xs ⟧ₙ)
    ⟦xs⟧≡2ⁿ*⟦xs⟧ₙ {n = suc n} xs =
        begin
            ⟦ 0∷ xs ⟧
        ≡⟨ ⟦xs⟧≡2ⁿ*⟦xs⟧ₙ (0∷ xs) ⟩
            (2 ^ n) * (2 * ⟦ xs ⟧ₙ)
        ≡⟨ sym (*-assoc (2 ^ n) 2 ⟦ xs ⟧ₙ) ⟩
            2 ^ n * 2 * ⟦ xs ⟧ₙ
        ≡⟨ cong (λ x → x * ⟦ xs ⟧ₙ) (*-comm (2 ^ n) 2) ⟩
            2 * (2 ^ n) * ⟦ xs ⟧ₙ
        ∎

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

    ⟦[]⟧≡⟦[]⟧ : ∀ {n A} → ⟦ [] {A} {suc n} ⟧ ≡ ⟦ [] {A} {n} ⟧
    ⟦[]⟧≡⟦[]⟧ {n} =
        begin
            ⟦ [] {n = suc n} ⟧
        ≡⟨ ⟦xs⟧≡2ⁿ*⟦xs⟧ₙ ([] {n = suc n}) ⟩
            2 * 2 ^ n * 0
        ≡⟨ *-right-zero (2 * 2 ^ n) ⟩
            0
        ≡⟨ sym (*-right-zero (2 ^ n)) ⟩
            2 ^ n * 0
        ≡⟨ sym (⟦xs⟧≡2ⁿ*⟦xs⟧ₙ ([] {n = n})) ⟩
            ⟦ [] {n = n} ⟧
        ∎

elemAt : ∀ {n A} → (xs : RandomAccessList A n) → Fin.Fin ⟦ xs ⟧ → A
elemAt {zero}  (     []) ()
elemAt {suc n} (     []) i  = elemAt {n} ([] {n = n}) (BLT.transportFin (⟦[]⟧≡⟦[]⟧ {n}) i)
elemAt         (  0∷ xs) i  with ⟦ 0∷ xs ⟧ | inspect ⟦_⟧ (0∷ xs)
elemAt         (  0∷ xs) () | zero  | _
elemAt         (  0∷ xs) i  | suc z | PropEq.[ eq ] = elemAt xs (BLT.transportFin (sym eq) i)
elemAt {n}     (x 1∷ xs) i  with (2 ^ n) ≤? Fin.toℕ i
elemAt {n}     (x 1∷ xs) i  | yes p rewrite splitIndex x xs = elemAt xs (Fin.reduce≥ i p)
elemAt         (x 1∷ xs) i  | no ¬p = BLT.elemAt x (Fin.fromℕ≤ (BLT.¬a≤b⇒b<a ¬p))
