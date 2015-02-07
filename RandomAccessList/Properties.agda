module RandomAccessList.Properties where

open import BuildingBlock
open import RandomAccessList


open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Product as Prod
open import Data.Product hiding (map)

open import Function
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; True; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning


--------------------------------------------------------------------------------
-- properties

_^_ : ℕ → ℕ → ℕ
a ^ zero  = 1
a ^ suc b = a * (a ^ b)

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

incr-2^n-lemma : ∀ {n A}
        → (x : BinaryLeafTree A n)
        → (xs : RandomAccessList A n)
        → ⟦ incr x xs ⟧ₙ ≡ suc ⟦ xs ⟧ₙ
incr-2^n-lemma x [] = refl
incr-2^n-lemma x (0∷ xs) = refl
incr-2^n-lemma x (y 1∷ xs) =
    begin
        2 * ⟦ incr (Node x y) xs ⟧ₙ
    ≡⟨ cong (_*_ 2) (incr-2^n-lemma (Node x y) xs) ⟩
        2 * (suc ⟦ xs ⟧ₙ)
    ≡⟨ +-*-suc 2 ⟦ xs ⟧ₙ ⟩
        2 + 2 * ⟦ xs ⟧ₙ
    ≡⟨ +-assoc 0 0 (2 + 2 * ⟦ xs ⟧ₙ) ⟩
        suc ⟦ y 1∷ xs ⟧ₙ
    ∎

incr-2^n : ∀ {n A}
        → (x : BinaryLeafTree A n)
        → (xs : RandomAccessList A n)
        → ⟦ incr x xs ⟧ ≡ 2 ^ n + ⟦ xs ⟧
incr-2^n {n} x xs =
    begin
        ⟦ incr x xs ⟧
    ≡⟨ ⟦xs⟧≡2ⁿ*⟦xs⟧ₙ (incr x xs) ⟩
        (2 ^ n) * ⟦ incr x xs ⟧ₙ
    ≡⟨ cong (_*_ (2 ^ n)) (incr-2^n-lemma x xs) ⟩
        2 ^ n * suc ⟦ xs ⟧ₙ
    ≡⟨ +-*-suc (2 ^ n) ⟦ xs ⟧ₙ ⟩
        2 ^ n + 2 ^ n * ⟦ xs ⟧ₙ
    ≡⟨ cong (_+_ (2 ^ n)) (sym (⟦xs⟧≡2ⁿ*⟦xs⟧ₙ xs)) ⟩
        2 ^ n + ⟦ xs ⟧
    ∎


++hom+ₙ : ∀ {A n}
        → (xs : RandomAccessList A n)
        → (ys : RandomAccessList A n)
        → ⟦ xs ++ ys ⟧ₙ ≡ ⟦ xs ⟧ₙ + ⟦ ys ⟧ₙ
++hom+ₙ (     []) (     ys) = refl
++hom+ₙ (  0∷ xs) (     []) = sym (+-right-identity (2 * ⟦ xs ⟧ₙ))
++hom+ₙ (  0∷ xs) (  0∷ ys) =
    begin
        2 * ⟦ xs ++ ys ⟧ₙ
    ≡⟨ cong (_*_ 2) (++hom+ₙ xs ys) ⟩
        2 * (⟦ xs ⟧ₙ + ⟦ ys ⟧ₙ)
    ≡⟨ distrib-left-*-+ 2 ⟦ xs ⟧ₙ ⟦ ys ⟧ₙ ⟩
        2 * ⟦ xs ⟧ₙ + 2 * ⟦ ys ⟧ₙ
    ∎
++hom+ₙ (  0∷ xs) (y 1∷ ys) =
    begin
        suc (2 * ⟦ xs ++ ys ⟧ₙ)
    ≡⟨ cong (suc ∘ _*_ 2) (++hom+ₙ xs ys) ⟩
        suc (2 * (⟦ xs ⟧ₙ + ⟦ ys ⟧ₙ))
    ≡⟨ cong suc (distrib-left-*-+ 2 ⟦ xs ⟧ₙ ⟦ ys ⟧ₙ) ⟩
        suc (2 * ⟦ xs ⟧ₙ + 2 * ⟦ ys ⟧ₙ)
    ≡⟨ sym (+-suc (2 * ⟦ xs ⟧ₙ) (2 * ⟦ ys ⟧ₙ)) ⟩
        2 * ⟦ xs ⟧ₙ + suc (2 * ⟦ ys ⟧ₙ)
    ∎
++hom+ₙ (x 1∷ xs) (     []) = cong suc (sym (+-right-identity (2 * ⟦ xs ⟧ₙ)))
++hom+ₙ (x 1∷ xs) (  0∷ ys) =
    begin
        suc (2 * ⟦ xs ++ ys ⟧ₙ)
    ≡⟨ cong (suc ∘ _*_ 2) (++hom+ₙ xs ys) ⟩
        suc (2 * (⟦ xs ⟧ₙ + ⟦ ys ⟧ₙ))
    ≡⟨ cong suc (distrib-left-*-+ 2 ⟦ xs ⟧ₙ ⟦ ys ⟧ₙ) ⟩
        suc (2 * ⟦ xs ⟧ₙ + 2 * ⟦ ys ⟧ₙ)
    ∎
++hom+ₙ (x 1∷ xs) (y 1∷ ys) =
    begin
        2 * ⟦ incr (Node x y) (xs ++ ys) ⟧ₙ
    ≡⟨ cong (_*_ 2) (incr-2^n-lemma (Node x y) (xs ++ ys)) ⟩
        2 * suc ⟦ xs ++ ys ⟧ₙ
    ≡⟨ cong (_*_ 2 ∘ suc) (++hom+ₙ xs ys) ⟩
        2 * suc (⟦ xs ⟧ₙ + ⟦ ys ⟧ₙ)
    ≡⟨ +-*-suc 2 (⟦ xs ⟧ₙ + ⟦ ys ⟧ₙ) ⟩
        suc (suc (2 * (⟦ xs ⟧ₙ + ⟦ ys ⟧ₙ)))
    ≡⟨ cong (suc ∘ suc) (distrib-left-*-+ 2 ⟦ xs ⟧ₙ ⟦ ys ⟧ₙ) ⟩
        suc (suc (2 * ⟦ xs ⟧ₙ + 2 * ⟦ ys ⟧ₙ))
    ≡⟨ cong suc (sym (+-suc (2 * ⟦ xs ⟧ₙ) (2 * ⟦ ys ⟧ₙ))) ⟩
        suc (2 * ⟦ xs ⟧ₙ + suc (2 * ⟦ ys ⟧ₙ))
    ∎

++hom+ : ∀ {n A}
        → (xs : RandomAccessList A n)
        → (ys : RandomAccessList A n)
        → ⟦ xs ++ ys ⟧ ≡ ⟦ xs ⟧ + ⟦ ys ⟧
++hom+ {n} xs ys =
    begin
        ⟦ xs ++ ys ⟧
    ≡⟨ ⟦xs⟧≡2ⁿ*⟦xs⟧ₙ (xs ++ ys) ⟩
        2 ^ n * ⟦ xs ++ ys ⟧ₙ
    ≡⟨ cong (_*_ (2 ^ n)) (++hom+ₙ xs ys) ⟩
        2 ^ n * (⟦ xs ⟧ₙ + ⟦ ys ⟧ₙ)
    ≡⟨ distrib-left-*-+ (2 ^ n) ⟦ xs ⟧ₙ ⟦ ys ⟧ₙ ⟩
        2 ^ n * ⟦ xs ⟧ₙ + 2 ^ n * ⟦ ys ⟧ₙ
    ≡⟨ cong₂ (λ x y → x + y) (sym (⟦xs⟧≡2ⁿ*⟦xs⟧ₙ xs)) (sym (⟦xs⟧≡2ⁿ*⟦xs⟧ₙ ys)) ⟩
        ⟦ xs ⟧ + ⟦ ys ⟧
    ∎
{-
borrow-+ : ∀ {A n}
        → (xs : RandomAccessList A n)
        → (p : False (null? xs))
        → ⟦ proj₁ (borrow xs p) ⟧ₙ + ⟦ proj₂ (borrow xs p) ⟧ₙ ≡ ⟦ xs ⟧ₙ
borrow-+ [] ()
borrow-+ (0∷ xs) p with null? xs
borrow-+ (0∷ xs) () | yes q
borrow-+ (0∷ xs) tt | no ¬q =
    begin
        2 * ⟦ proj₁ (borrow xs (fromWitnessFalse ¬q)) ⟧ₙ + 2 * ⟦ proj₂ (borrow xs (fromWitnessFalse ¬q)) ⟧ₙ
    ≡⟨ sym (distrib-left-*-+ 2 ⟦ proj₁ (borrow xs (fromWitnessFalse ¬q)) ⟧ₙ ⟦ proj₂ (borrow xs (fromWitnessFalse ¬q)) ⟧ₙ) ⟩
        2 * (⟦ proj₁ (borrow xs (fromWitnessFalse ¬q)) ⟧ₙ + ⟦ proj₂ (borrow xs (fromWitnessFalse ¬q)) ⟧ₙ)
    ≡⟨ cong (_*_ 2) (borrow-+ xs (fromWitnessFalse ¬q)) ⟩
        2 * ⟦ xs ⟧ₙ
    ∎
borrow-+ (x 1∷ xs) p = sym (++-+ [] (x 1∷ xs))

++∘borrow-id : ∀ {A n}
                → (xs : RandomAccessList A n)
                → (p : False (null? xs))
                → (uncurry _++_ (borrow xs p)) ≡ xs
++∘borrow-id [] ()
++∘borrow-id (0∷ xs) p with null? xs
++∘borrow-id (0∷ xs) () | yes q
++∘borrow-id (0∷ xs) tt | no ¬q with borrow xs (fromWitnessFalse ¬q) | inspect (borrow xs) (fromWitnessFalse ¬q)
++∘borrow-id (0∷ xs) tt | no ¬q | ys , xs' | PropEq.[ eq ] = cong 0∷_ (
    begin
        uncurry _++_ (ys , xs')
    ≡⟨ cong (uncurry _++_) (sym eq) ⟩
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
-}
