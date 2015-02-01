module RandomAccessList where

open import BuildingBlock

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Product as Prod
open import Data.Product hiding (map)

open import Function

open import Relation.Nullary.Negation
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; True; fromWitnessFalse)

open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym; inspect)
open PropEq.≡-Reasoning

-- parameterized by the level of the least significant digit
data RandomAccessList (A : Set) : ℕ → Set where
    []   : ∀ {n} → RandomAccessList A n
    0∷_  : ∀ {n} → RandomAccessList A (suc n) → RandomAccessList A n
    _1∷_ : ∀ {n} → BinaryLeafTree A n → RandomAccessList A (suc n) → RandomAccessList A n

0∷-lift : ∀ {A n} → RandomAccessList A n → (m : ℕ) → m ≤ n → RandomAccessList A m
0∷-lift {n = zero} xs zero z≤n = xs
0∷-lift {n = zero} xs (suc m) ()
0∷-lift {n = suc n} xs zero z≤n = 0∷ (0∷-lift xs (suc zero) (s≤s z≤n))
0∷-lift {n = suc n} xs (suc m) (s≤s m≤n) = 0∷-lift xs (suc m) (s≤s m≤n)

--------------------------------------------------------------------------------
-- examples

private
    a : RandomAccessList ℕ 0
    a = Leaf zero 1∷ []
    b : RandomAccessList ℕ 1
    b = (Node (Leaf zero) (Leaf zero)) 1∷ []
    c : RandomAccessList ℕ 1
    c = 0∷ ((Node (Node (Leaf zero) (Leaf zero)) (Node (Leaf zero) (Leaf zero))) 1∷ [])

--------------------------------------------------------------------------------
-- to ℕ

⟦_⟧ : ∀ {A n} → RandomAccessList A n → ℕ
⟦   []    ⟧ = zero
⟦   0∷ xs ⟧ = 2 * ⟦ xs ⟧
⟦ _ 1∷ xs ⟧ = 1 + 2 * ⟦ xs ⟧

n*a≡0⇒a≡0 : (a n : ℕ) → 0 < n → n * a ≡ 0 → a ≡ 0
n*a≡0⇒a≡0 a       zero    ()        n*a≡0
n*a≡0⇒a≡0 zero    (suc n) (s≤s z≤n) a+n*a≡0 = refl
n*a≡0⇒a≡0 (suc a) (suc n) (s≤s z≤n) ()


--------------------------------------------------------------------------------
-- predicates

Null? : ∀ {A n} → (xs : RandomAccessList A n) → Dec (⟦ xs ⟧ ≡ 0)
Null?    []     = yes refl
Null? (  0∷ xs) with Null? xs
Null? (  0∷ xs) | yes p = yes (cong (_*_ 2) p)
Null? (  0∷ xs) | no ¬p = no (¬p ∘ (n*a≡0⇒a≡0 ⟦ xs ⟧ 2 (s≤s z≤n)))
Null? (x 1∷ xs) = no (λ ())

--------------------------------------------------------------------------------
-- operations

-- numerical: +1
-- container: insertion
incr : ∀ {A n} → BinaryLeafTree A n → RandomAccessList A n → RandomAccessList A n
incr a    []     = a 1∷ []
incr a (  0∷ xs) = a 1∷ xs
incr a (x 1∷ xs) = 0∷ (incr (Node a x) xs)

-- not needed for the moment
-- numerical: carry
carry : ∀ {A n} → BinaryLeafTree A n → BinaryLeafTree A n → BinaryLeafTree A (suc n)
carry x y = Node x y

-- numerical: +
-- container: merge
_++_ : ∀ {A n} → RandomAccessList A n → RandomAccessList A n → RandomAccessList A n
[]        ++ ys        = ys
(  0∷ xs) ++ []        =   0∷ xs
(  0∷ xs) ++ (  0∷ ys) =   0∷ (xs ++ ys)
(  0∷ xs) ++ (x 1∷ ys) = x 1∷ (xs ++ ys)
(x 1∷ xs) ++ []        = x 1∷ xs
(x 1∷ xs) ++ (  0∷ ys) = x 1∷ (xs ++ ys)
(x 1∷ xs) ++ (y 1∷ ys) =   0∷ (incr (Node x y) (xs ++ ys))

-- borrow from the first non-zero digit, and splits it like so (1:xs)
-- numerical: borrow
borrow : ∀ {A n} → (xs : RandomAccessList A n) → False (Null? xs) → RandomAccessList A n × RandomAccessList A n
borrow [] ()
borrow (0∷ xs) q with Null? xs
borrow (0∷ xs) () | yes p
borrow (0∷ xs) tt | no ¬p = Prod.map 0∷_ 0∷_ (borrow xs (fromWitnessFalse ¬p))
borrow {n = n} (x 1∷ xs) q = x 1∷ [] , 0∷ xs

-- numerical: -1
-- container: deletion{-
decr : ∀ {A n} → (xs : RandomAccessList A n) → False (Null? xs) → RandomAccessList A n
decr [] ()
decr (0∷ xs) q with Null? xs
decr (0∷ xs) () | yes p
decr (0∷ xs) tt | no ¬p = 0∷ (proj₂ (borrow xs (fromWitnessFalse ¬p)))
decr (x 1∷ xs) q = 0∷ xs

--------------------------------------------------------------------------------
-- properties

incr-+1 : ∀ {A n}
        → (x : BinaryLeafTree A n)
        → (xs : RandomAccessList A n)
        → ⟦ incr x xs ⟧ ≡ suc ⟦ xs ⟧
incr-+1 x [] = refl
incr-+1 x (0∷ xs) = refl
incr-+1 x (y 1∷ xs) =
    begin
        ⟦ incr x (y 1∷ xs) ⟧
    ≡⟨ refl ⟩
        ⟦ 0∷ incr (Node x y) xs ⟧
    ≡⟨ refl ⟩
        2 * ⟦ incr (Node x y) xs ⟧
    ≡⟨ cong (_*_ 2) (incr-+1 (Node x y) xs) ⟩
        2 * (suc ⟦ xs ⟧)
    ≡⟨ +-*-suc 2 ⟦ xs ⟧ ⟩
        2 + 2 * ⟦ xs ⟧
    ≡⟨ +-assoc 0 0 (2 + 2 * ⟦ xs ⟧) ⟩
        suc (1 + 2 * ⟦ xs ⟧)
    ≡⟨ refl ⟩
        suc ⟦ y 1∷ xs ⟧
    ∎

distrib-left-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
distrib-left-*-+ m n o =
        begin
            m * (n + o)
        ≡⟨ *-comm m (n + o) ⟩
            (n + o) * m
        ≡⟨ distribʳ-*-+ m n o ⟩
            n * m + o * m
        ≡⟨ cong (flip _+_ (o * m)) (*-comm n m) ⟩
            m * n + o * m
        ≡⟨ cong (_+_ (m * n)) (*-comm o m) ⟩
            m * n + m * o
        ∎

++-+ : ∀ {A n}
    → (xs : RandomAccessList A n)
    → (ys : RandomAccessList A n)
    → ⟦ xs ++ ys ⟧ ≡ ⟦ xs ⟧ + ⟦ ys ⟧
++-+ []        ys        = refl
++-+ (  0∷ xs) []        = sym (+-right-identity (⟦ xs ⟧ + (⟦ xs ⟧ + 0)))
++-+ (  0∷ xs) (  0∷ ys) =
    begin
        ⟦ (0∷ xs) ++ (0∷ ys) ⟧
    ≡⟨ cong (_*_ 2) (++-+ xs ys) ⟩
        2 * (⟦ xs ⟧ + ⟦ ys ⟧)
    ≡⟨ distrib-left-*-+ 2 ⟦ xs ⟧ ⟦ ys ⟧ ⟩
        ⟦ 0∷ xs ⟧ + ⟦ 0∷ ys ⟧
    ∎
++-+ (  0∷ xs) (y 1∷ ys) =
    begin
        ⟦ (0∷ xs) ++ (y 1∷ ys) ⟧
    ≡⟨ cong suc (cong (_*_ 2) (++-+ xs ys)) ⟩
        1 + (2 * (⟦ xs ⟧ + ⟦ ys ⟧))
    ≡⟨ cong suc (distrib-left-*-+ 2 ⟦ xs ⟧ ⟦ ys ⟧) ⟩
        1 + (2 * ⟦ xs ⟧ + 2 * ⟦ ys ⟧)
    ≡⟨ sym (+-suc (⟦ xs ⟧ + (⟦ xs ⟧ + 0)) (⟦ ys ⟧ + (⟦ ys ⟧ + 0))) ⟩
        2 * ⟦ xs ⟧ + (1 + 2 * ⟦ ys ⟧)
    ≡⟨ cong (_+_ (2 * ⟦ xs ⟧)) refl ⟩
        ⟦ 0∷ xs ⟧ + ⟦ y 1∷ ys ⟧
    ∎
++-+ (x 1∷ xs) []        = sym (+-right-identity (suc (⟦ xs ⟧ + (⟦ xs ⟧ + 0))))
++-+ (x 1∷ xs) (  0∷ ys) =
    begin
        1 + 2 * ⟦ xs ++ ys ⟧
    ≡⟨ cong (λ z → suc (2 * z)) (++-+ xs ys) ⟩
        1 + 2 * (⟦ xs ⟧ + ⟦ ys ⟧)
    ≡⟨ cong suc (distrib-left-*-+ 2 ⟦ xs ⟧ ⟦ ys ⟧) ⟩
        1 + (2 * ⟦ xs ⟧ + 2 * ⟦ ys ⟧)
    ≡⟨ sym (+-assoc 0 0 (suc (⟦ xs ⟧ + (⟦ xs ⟧ + 0) + (⟦ ys ⟧ + (⟦ ys ⟧ + 0))))) ⟩
        (1 + 2 * ⟦ xs ⟧) + 2 * ⟦ ys ⟧
    ∎
++-+ (x 1∷ xs) (y 1∷ ys) =
    begin
        2 * ⟦ incr (Node x y) (xs ++ ys) ⟧
    ≡⟨ cong (_*_ 2) (incr-+1 (Node x y) (xs ++ ys)) ⟩
        2 * suc ⟦ xs ++ ys ⟧
    ≡⟨ cong (λ w → 2 * suc w) (++-+ xs ys) ⟩
        2 * (1 + (⟦ xs ⟧ + ⟦ ys ⟧))
    ≡⟨ distrib-left-*-+ 2 1 (⟦ xs ⟧ + ⟦ ys ⟧) ⟩
        2 + 2 * (⟦ xs ⟧ + ⟦ ys ⟧)
    ≡⟨ cong (_+_ 2) (distrib-left-*-+ 2 ⟦ xs ⟧ ⟦ ys ⟧) ⟩
        2 + (2 * ⟦ xs ⟧ + 2 * ⟦ ys ⟧)
    ≡⟨ cong suc (+-assoc 0 0 (suc (⟦ xs ⟧ + (⟦ xs ⟧ + 0) + (⟦ ys ⟧ + (⟦ ys ⟧ + 0))))) ⟩
        1 + (1 + (2 * ⟦ xs ⟧ + 2 * ⟦ ys ⟧))
    ≡⟨ cong suc (+-assoc 0 0 (suc (⟦ xs ⟧ + (⟦ xs ⟧ + 0) + (⟦ ys ⟧ + (⟦ ys ⟧ + 0))))) ⟩
        1 + ((1 + 2 * ⟦ xs ⟧) + 2 * ⟦ ys ⟧)
    ≡⟨ cong (λ w → 1 + (w + 2 * ⟦ ys ⟧)) (+-comm 1 (⟦ xs ⟧ + (⟦ xs ⟧ + 0))) ⟩
        1 + ((2 * ⟦ xs ⟧ + 1) + 2 * ⟦ ys ⟧)
    ≡⟨ cong suc (+-assoc (⟦ xs ⟧ + (⟦ xs ⟧ + 0)) 1 (⟦ ys ⟧ + (⟦ ys ⟧ + 0))) ⟩
        1 + (2 * ⟦ xs ⟧ + (1 + 2 * ⟦ ys ⟧))
    ≡⟨ refl ⟩
        ⟦ x 1∷ xs ⟧ + ⟦ y 1∷ ys ⟧
    ∎

borrow-+ : ∀ {A n}
        → (xs : RandomAccessList A n)
        → (p : False (Null? xs))
        → ⟦ proj₁ (borrow xs p) ⟧ + ⟦ proj₂ (borrow xs p) ⟧ ≡ ⟦ xs ⟧
borrow-+ [] ()
borrow-+ (0∷ xs) p with Null? xs
borrow-+ (0∷ xs) () | yes q
borrow-+ (0∷ xs) tt | no ¬q =
    begin
        2 * ⟦ proj₁ (borrow xs (fromWitnessFalse ¬q)) ⟧ + 2 * ⟦ proj₂ (borrow xs (fromWitnessFalse ¬q)) ⟧
    ≡⟨ sym (distrib-left-*-+ 2 ⟦ proj₁ (borrow xs (fromWitnessFalse ¬q)) ⟧ ⟦ proj₂ (borrow xs (fromWitnessFalse ¬q)) ⟧) ⟩
        2 * (⟦ proj₁ (borrow xs (fromWitnessFalse ¬q)) ⟧ + ⟦ proj₂ (borrow xs (fromWitnessFalse ¬q)) ⟧)
    ≡⟨ cong (_*_ 2) (borrow-+ xs (fromWitnessFalse ¬q)) ⟩
        2 * ⟦ xs ⟧
    ∎
borrow-+ (x 1∷ xs) p = sym (++-+ [] (x 1∷ xs))

++∘borrow-id : ∀ {A n}
                → (xs : RandomAccessList A n)
                → (p : False (Null? xs))
                → (uncurry _++_ (borrow xs p)) ≡ xs
++∘borrow-id [] ()
++∘borrow-id (0∷ xs) p with Null? xs
++∘borrow-id (0∷ xs) () | yes q
++∘borrow-id (0∷ xs) tt | no ¬q with borrow xs (fromWitnessFalse ¬q) | inspect (borrow xs) (fromWitnessFalse ¬q)
++∘borrow-id (0∷ xs) tt | no ¬q | ys , xs' | PropEq.[ eq ] = cong 0∷_ (
    begin
        uncurry _++_ (ys , xs')
    ≡⟨ cong (uncurry _++_) {!   !} ⟩
        uncurry _++_ (borrow xs (fromWitnessFalse ¬q))
    ≡⟨ ++∘borrow-id xs (fromWitnessFalse ¬q) ⟩
        xs
    ∎)
++∘borrow-id (x 1∷ xs) p = refl

{-
begin
    {!   !}
≡⟨ {!   !} ⟩
    {!   !}
≡⟨ {!   !} ⟩
    {!   !}
≡⟨ {!   !} ⟩
    {!   !}
≡⟨ {!   !} ⟩
    {!   !}
∎
-}
