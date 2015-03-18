module ZerolessRAL where

open import ZerolessRAL.Core
open import ZerolessRAL.Core.Properties
open import BuildingBlock.BinaryLeafTree using (BinaryLeafTree; Node; Leaf; split)
import BuildingBlock.BinaryLeafTree as BLT

open import Data.Fin using (Fin; fromℕ; fromℕ≤; reduce≥; toℕ)
import      Data.Fin as Fin
open import Data.Nat
open import Data.Nat.DivMod
-- open import Data.Nat.Properties.Simple
open import Data.Nat.Etc
open import Data.Product
open import Function
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

-- cons
consₙ : ∀ {n A} → BinaryLeafTree A n → 1-2-RAL A n → 1-2-RAL A n
consₙ a (         []) = a     1∷ []
consₙ a (x     1∷ xs) = a , x 2∷ xs
consₙ a (x , y 2∷ xs) = a     1∷ consₙ (Node x y) xs

cons : ∀ {A} → A → 1-2-RAL A 0 → 1-2-RAL A 0
cons a xs = consₙ (Leaf a) xs

-- head
headₙ : ∀ {n A} → (xs : 1-2-RAL A n) → ⟦ xs ⟧ ≢ 0 → BinaryLeafTree A n
headₙ {n} {A} []    p = contradiction (⟦[]⟧≡0 ([] {A} {n}) refl) p
headₙ (x     1∷ xs) p = x
headₙ (x , y 2∷ xs) p = x

head : ∀ {A} → (xs : 1-2-RAL A 0) → ⟦ xs ⟧ ≢ 0 → A
head xs p = BLT.head (headₙ xs p)

-- tail
tailₙ : ∀ {n A} → (xs : 1-2-RAL A n) → ⟦ xs ⟧ ≢ 0 → 1-2-RAL A n
tailₙ []            p = []
tailₙ (x 1∷ xs) p with ⟦ xs ⟧ ≟ 0
tailₙ (x 1∷ xs) p | yes q = []
tailₙ (x 1∷ xs) p | no ¬q =
    let y₀ = proj₁ (split (headₙ xs ¬q))
        y₁ = proj₂ (split (headₙ xs ¬q))
    in  y₀ , y₁ 2∷ tailₙ xs ¬q
tailₙ (x , y 2∷ xs) p = y 1∷ xs

tail : ∀ {A} → (xs : 1-2-RAL A 0) → ⟦ xs ⟧ ≢ 0 → 1-2-RAL A 0
tail = tailₙ

--------------------------------------------------------------------------------
-- Searching
--------------------------------------------------------------------------------

{-
data Occurrence : ℕ → Set where
    here : ∀ {n b} → ℕ → Fin (b * 2 ^ n) → Occurrence n
    there : ∀ {n} → Occurrence n

transportFin : ∀ {a b} → a ≡ b → Fin a → Fin b
transportFin refl i = i

search : ∀ {n A} → (xs : 1-2-RAL A n) → ℕ → Occurrence n
search []            i = there
search {n} (x     1∷ xs) i with (1 * 2 ^ n) ≤? i
search (x 1∷ xs) i | yes p = there
search {n} (x 1∷ xs) i | no ¬p = here 0 (fromℕ≤ (m≰n⇒n<m (1 * 2 ^ n) i ¬p))
search {n} (x , y 2∷ xs) i with (2 * 2 ^ n) ≤? i
search (x , y 2∷ xs) i | yes p = there
search {n} (x , y 2∷ xs) i | no ¬p with i divMod (2 ^ n)
search (x , y 2∷ xs) i | no ¬p | result zero remainder _ = here zero {!   !}
search (x , y 2∷ xs) i | no ¬p | result (suc quotient) remainder _ = {!   !}

elemAt : ∀ {n A} → (xs : 1-2-RAL A n) → Fin ⟦ xs ⟧ → A
elemAt {n} {A} []    i = contradiction (transportFin (⟦[]⟧≡0 ([] {A} {n}) refl) i) (λ ())
elemAt (x     1∷ xs) i = {!   !}
elemAt (x , y 2∷ xs) i = {!   !}

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
{-
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
-}
-- reduce≥ : ∀ {m n} (i : Fin (m N+ n)) (i≥m : toℕ i N≥ m) → Fin n
-- i : 2 * 2 ^ n + (2 * 2 ^ n) * ⟦ xs ⟧ₙ
-- m : 2 ^ n
-}
