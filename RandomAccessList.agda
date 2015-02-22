module RandomAccessList where

open import RandomAccessList.Core
open import RandomAccessList.Core.Properties
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf)
import BuildingBlock.BinaryLeafTree as BLT

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; fromℕ≤; reduce≥; toℕ)
import      Data.Fin as Fin
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Nat.Etc
open import Data.Product as Prod
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------
-- predicates

null : ∀ {n A} → RandomAccessList A n → Set
null []        = ⊤
null (  0∷ xs) = null xs
null (x 1∷ xs) = ⊥

null? : ∀ {n A} → (xs : RandomAccessList A n) → Dec (null xs)
null? []        = yes tt
null? (  0∷ xs) = null? xs
null? (x 1∷ xs) = no (λ z → z)

--------------------------------------------------------------------------------
-- Operations

consₙ : ∀ {n A} → BinaryLeafTree A n → RandomAccessList A n → RandomAccessList A n
consₙ a []        = a 1∷ []
consₙ a (  0∷ xs) = a 1∷ xs
consₙ a (x 1∷ xs) =   0∷ (consₙ (Node a x) xs)

cons : ∀ {A} → A → RandomAccessList A 0 → RandomAccessList A 0
cons a xs = consₙ (Leaf a) xs

headₙ :  ∀ {n A}
        → (xs : RandomAccessList A n)
        → False (null? xs)
        → BinaryLeafTree A n
headₙ []        ()
headₙ (  0∷ xs) p  with null? xs
headₙ (  0∷ xs) () | yes q
headₙ (  0∷ xs) p  | no ¬q = proj₁ (BLT.split (headₙ xs (fromWitnessFalse ¬q)))
headₙ (x 1∷ xs) p  = x


head :  ∀ {n A}
        → (xs : RandomAccessList A n)
        → False (null? xs)
        → A
head []        ()
head (  0∷ xs) p  with null? xs
head (  0∷ xs) () | yes q
head (  0∷ xs) p  | no ¬q = head xs (fromWitnessFalse ¬q)
head (x 1∷ xs) p  = BLT.head x


tailₙ : ∀ {n A}
        → (xs : RandomAccessList A n)
        → False (null? xs)
        → RandomAccessList A n
tailₙ []        ()
tailₙ (  0∷ xs) p  with null? xs
tailₙ (  0∷ xs) () | yes q
tailₙ (  0∷ xs) p  | no ¬q = proj₂ (BLT.split (headₙ xs (fromWitnessFalse ¬q))) 1∷ tailₙ xs (fromWitnessFalse ¬q)
tailₙ (x 1∷ xs) p  = 0∷ xs

tail : ∀ {n A}
        → (xs : RandomAccessList A n)
        → False (null? xs)
        → RandomAccessList A 0
tail {zero } xs p = tailₙ xs p
tail {suc n} xs p = tail (0∷ xs) p


--------------------------------------------------------------------------------
-- Searching

transportFin : ∀ {a b} → a ≡ b → Fin a → Fin b
transportFin refl i = i

splitIndex : ∀ {n A} → (x : BinaryLeafTree A n) → (xs : RandomAccessList A (suc n)) → ⟦ x 1∷ xs ⟧ ≡ (2 ^ n) + ⟦ xs ⟧
splitIndex {n} x xs =
    begin
        2 ^ n * suc (2 * ⟦ xs ⟧ₙ)
    ≡⟨ +-*-suc (2 ^ n) (2 * ⟦ xs ⟧ₙ) ⟩
        2 ^ n + 2 ^ n * (2 * ⟦ xs ⟧ₙ)
    ≡⟨ cong (_+_ (2 ^ n)) (sym (*-assoc (2 ^ n) 2 ⟦ xs ⟧ₙ)) ⟩
        2 ^ n + 2 ^ n * 2 * ⟦ xs ⟧ₙ
    ≡⟨ cong (λ w → 2 ^ n + w * ⟦ xs ⟧ₙ) (*-comm (2 ^ n) 2) ⟩
        2 ^ n + (2 * 2 ^ n) * ⟦ xs ⟧ₙ
    ∎

elemAt : ∀ {n A} → (xs : RandomAccessList A n) → Fin ⟦ xs ⟧ → A
elemAt {zero}  (     []) ()
elemAt {suc n} {A} ( []) i  = elemAt {n} ([] {n = n}) (transportFin (⟦[]⟧≡⟦[]⟧ {n} {A}) i)
elemAt         (  0∷ xs) i  with ⟦ 0∷ xs ⟧ | inspect ⟦_⟧ (0∷ xs)
elemAt         (  0∷ xs) () | zero  | _
elemAt {n}     (  0∷ xs) i  | suc z | PropEq.[ eq ] = elemAt xs (transportFin (trans (sym eq) (⟦0∷xs⟧≡⟦xs⟧ xs)) i)
elemAt {n}     (x 1∷ xs) i  with (2 ^ n) ≤? toℕ i
elemAt {n}     (x 1∷ xs) i  | yes p rewrite splitIndex x xs = elemAt xs (reduce≥ i p)
elemAt         (x 1∷ xs) i  | no ¬p = BLT.elemAt x (fromℕ≤ (BLT.¬a≤b⇒b<a ¬p))
