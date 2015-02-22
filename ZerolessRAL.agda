module ZerolessRAL where

open import ZerolessRAL.Core
-- open import RandomAccessList.Properties
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf; split)
import BuildingBlock.BinaryLeafTree as BLT

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; fromℕ≤; reduce≥; toℕ)
import      Data.Fin as Fin
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Nat.Etc
open import Data.Product
open import Function
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------
-- predicates

null : ∀ {n A} → 1-2-RAL A n → Set
null (         []) = ⊤
null (x     1∷ xs) = ⊥
null (x , y 2∷ xs) = ⊥

null? : ∀ {n A} → (xs : 1-2-RAL A n) → Dec (null xs)
null? (         []) = yes tt
null? (x     1∷ xs) = no (λ z → z)
null? (x , y 2∷ xs) = no (λ z → z)

--------------------------------------------------------------------------------
-- Operations

-- cons
consₙ : ∀ {n A} → BinaryLeafTree A n → 1-2-RAL A n → 1-2-RAL A n
consₙ a (         []) = a     1∷ []
consₙ a (x     1∷ xs) = a , x 2∷ xs
consₙ a (x , y 2∷ xs) = a     1∷ consₙ (Node x y) xs

cons : ∀ {A} → A → 1-2-RAL A 0 → 1-2-RAL A 0
cons a xs = consₙ (Leaf a) xs

-- head
headₙ : ∀ {n A} → (xs : 1-2-RAL A n) → False (null? xs) → BinaryLeafTree A n
headₙ []            ()
headₙ (x     1∷ xs) p  = x
headₙ (x , y 2∷ xs) p  = x

head : ∀ {A} → (xs : 1-2-RAL A 0) → False (null? xs) → A
head xs p = BLT.head (headₙ xs p)


spread : ∀ {n A} → (xs : 1-2-RAL A (suc n)) → False (null? xs) → 1-2-RAL A (suc n) → 1-2-RAL A n
spread []                      () rest
spread (Node x₀ x₁      1∷ xs) p  rest = x₀ , x₁ 2∷ rest
spread (Node x₀ x₁  , y 2∷ xs) p  rest = x₀ , x₁ 2∷ rest

-- tail
tailₙ : ∀ {n A} → (xs : 1-2-RAL A n) → False (null? xs) → 1-2-RAL A n
tailₙ []            ()
tailₙ (x     1∷ xs) p  with null? xs
tailₙ (x     1∷ xs) p  | yes q = []
tailₙ (x     1∷ xs) p  | no ¬q = spread xs (fromWitnessFalse ¬q) (tailₙ xs (fromWitnessFalse ¬q))
tailₙ (x , y 2∷ xs) p          = y 1∷ xs

tail : ∀ {A} → (xs : 1-2-RAL A 0) → False (null? xs) → 1-2-RAL A 0
tail = tailₙ

--------------------------------------------------------------------------------
-- Searching

transportFin : ∀ {a b} → a ≡ b → Fin a → Fin b
transportFin refl i = i

splitIndex1∷ : ∀ {n A} → (x : BinaryLeafTree A n) → (xs : 1-2-RAL A (suc n)) → ⟦ x 1∷ xs ⟧ ≡ (2 ^ n) + ⟦ xs ⟧
splitIndex1∷ {n} x xs =
    begin
        ⟦ x 1∷ xs ⟧
    ≡⟨ +-*-suc (2 ^ n) (2 * ⟦ xs ⟧ₙ) ⟩
        2 ^ n + 2 ^ n * (2 * ⟦ xs ⟧ₙ)
    ≡⟨ cong (_+_ (2 ^ n)) (sym (*-assoc (2 ^ n) 2 ⟦ xs ⟧ₙ)) ⟩
        2 ^ n + 2 ^ n * 2 * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ w → 2 ^ n + w * ⟦ xs ⟧ₙ) (*-comm (2 ^ n) 2) ⟩
        (2 ^ n) + ⟦ xs ⟧
    ∎

n+n≡2*n : (n : ℕ) → n + n ≡ 2 * n
n+n≡2*n n = cong (_+_ n) (sym (+-right-identity n))

splitIndex2∷ : ∀ {n A}
            → (x : BinaryLeafTree A n)
            → (y : BinaryLeafTree A n)
            → (xs : 1-2-RAL A (suc n)) → ⟦ x , y 2∷ xs ⟧ ≡ 2 * (2 ^ n) + ⟦ xs ⟧
splitIndex2∷ {n} x y xs =
    begin
        ⟦ x , y 2∷ xs ⟧
    ≡⟨ +-*-suc (2 ^ n) (suc (2 * ⟦ xs ⟧ₙ)) ⟩
        2 ^ n + 2 ^ n * suc (2 * ⟦ xs ⟧ₙ)
    ≡⟨ cong (_+_ (2 ^ n)) (+-*-suc (2 ^ n) (2 * ⟦ xs ⟧ₙ)) ⟩
        2 ^ n + (2 ^ n + 2 ^ n * (2 * ⟦ xs ⟧ₙ))
    ≡⟨ sym (+-assoc (2 ^ n) (2 ^ n) (2 ^ n * (2 * ⟦ xs ⟧ₙ))) ⟩
        2 ^ n + 2 ^ n + 2 ^ n * (2 * ⟦ xs ⟧ₙ)
    ≡⟨ cong (λ w → 2 ^ n + 2 ^ n + w) (sym (*-assoc (2 ^ n) 2 ⟦ xs ⟧ₙ)) ⟩
        2 ^ n + 2 ^ n + 2 ^ n * 2 * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ w → 2 ^ n + 2 ^ n + w * ⟦ xs ⟧ₙ) (*-comm (2 ^ n) 2) ⟩
        2 ^ n + 2 ^ n + 2 * 2 ^ n * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ w → w + 2 * 2 ^ n * ⟦ xs ⟧ₙ) (n+n≡2*n (2 ^ n)) ⟩
        2 * 2 ^ n + ⟦ xs ⟧
    ∎

elemAt : ∀ {n A} → (xs : 1-2-RAL A n) → Fin ⟦ xs ⟧ → A
elemAt     (         []) ()
elemAt {n} (x     1∷ xs) i with  (2 ^ n) ≤? toℕ i
elemAt {n} (x     1∷ xs) i | yes p rewrite splitIndex1∷ x xs = elemAt xs (reduce≥ i p)
elemAt     (x     1∷ xs) i | no ¬p = BLT.elemAt x (fromℕ≤ (BLT.¬a≤b⇒b<a ¬p))
elemAt {n} (x , y 2∷ xs) i with  (2 * (2 ^ n)) ≤? toℕ i
elemAt     (x , y 2∷ xs) i | yes p rewrite splitIndex2∷ x y xs = elemAt xs (reduce≥ i p)
elemAt {n} (x , y 2∷ xs) i | no ¬p with (2 ^ n) ≤? toℕ i
elemAt     (x , y 2∷ xs) i | no ¬p | yes q rewrite splitIndex2∷ x y xs = BLT.elemAt y {!   !} -- y
elemAt     (x , y 2∷ xs) i | no ¬p | no ¬q = BLT.elemAt x (fromℕ≤ (BLT.¬a≤b⇒b<a ¬q)) -- x
-- reduce≥ : ∀ {m n} (i : Fin (m N+ n)) (i≥m : toℕ i N≥ m) → Fin n
-- i : 2 * 2 ^ n + (2 * 2 ^ n) * ⟦ xs ⟧ₙ
-- m : 2 ^ n
