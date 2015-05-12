module Data.Num.Bij.Convert where

open import Data.Num.Bij
open import Data.Num.Bij.Properties

open import Data.List hiding ([_])
open import Relation.Binary
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Etc

open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; sym; cong; trans)
open PropEq.≡-Reasoning
import Level

{-
-- to ℕ, instance of Conversion
instance convNat : Conversion ℕ
convNat = conversion [_]' !_!'
    where   [_]' : ℕ → Bij
            [ zero  ]' = []
            [ suc n ]' = incrB [ n ]'
            !_!' : Bij → ℕ
            ! []       !' = 0
            ! one ∷ xs !' = 1 + 2 * ! xs !'
            ! two ∷ xs !' = 2 + 2 * ! xs !'
-}


-- Digit ⇒ ℕ
D[_]ℕ : DigitB → ℕ
D[ one ]ℕ = 1
D[ two ]ℕ = 2

-- ℕ ⇔ Bij
[_]B : ℕ → Bij
[ zero  ]B = []
[ suc n ]B = incrB [ n ]B


[_]ℕ : Bij → ℕ
[ []       ]ℕ = 0
[ one ∷ xs ]ℕ = 1 + 2 * [ xs ]ℕ
[ two ∷ xs ]ℕ = 2 + 2 * [ xs ]ℕ


-- properties
[]ℕ-∷-hom : ∀ x xs → [ x ∷ xs ]ℕ ≡ D[ x ]ℕ + 2 * [ xs ]ℕ
[]ℕ-∷-hom one _ = refl
[]ℕ-∷-hom two _ = refl


[]ℕ-incrB-hom : ∀ xs → [ incrB xs ]ℕ ≡ suc [ xs ]ℕ
[]ℕ-incrB-hom [] = refl
[]ℕ-incrB-hom (one ∷ xs) = refl
[]ℕ-incrB-hom (two ∷ xs) =
    begin
        suc (2 * [ incrB xs ]ℕ)
    ≡⟨ cong (λ x → suc (2 * x)) ([]ℕ-incrB-hom xs) ⟩
        suc (suc ([ xs ]ℕ + suc ([ xs ]ℕ + 0)))
    ≡⟨ cong (λ x → suc (suc x)) (+-suc [ xs ]ℕ ([ xs ]ℕ + 0)) ⟩
        suc (suc (suc (2 * [ xs ]ℕ)))
    ∎


[]ℕ-+B-hom : ∀ xs ys → [ xs +B ys ]ℕ ≡ [ xs ]ℕ + [ ys ]ℕ
[]ℕ-+B-hom [] ys = refl
[]ℕ-+B-hom (x ∷ xs) [] = sym (+-right-identity [ x ∷ xs ]ℕ)
[]ℕ-+B-hom (one ∷ xs) (one ∷ ys) =
    begin
        2 + 2 * [ xs +B ys ]ℕ
    ≡⟨ cong (λ x → 2 + 2 * x) ([]ℕ-+B-hom xs ys) ⟩
        2 + 2 * ([ xs ]ℕ + [ ys ]ℕ)
    ≡⟨ cong (λ x → 2 + x) (distrib-left-*-+ 2 [ xs ]ℕ [ ys ]ℕ) ⟩
        2 + (2 * [ xs ]ℕ + 2 * [ ys ]ℕ)
    ≡⟨ cong suc (sym (+-suc (2 * [ xs ]ℕ) (2 * [ ys ]ℕ))) ⟩
        suc (2 * [ xs ]ℕ + suc (2 * [ ys ]ℕ))
    ∎
[]ℕ-+B-hom (one ∷ xs) (two ∷ ys) =
    begin
        1 + 2 * [ incrB (xs +B ys) ]ℕ
    ≡⟨ cong (λ x → 1 + 2 * x) ([]ℕ-incrB-hom (xs +B ys)) ⟩
        1 + 2 * (1 + [ xs +B ys ]ℕ)
    ≡⟨ cong (λ x → 1 + 2 * (1 + x)) ([]ℕ-+B-hom xs ys) ⟩
        1 + 2 * suc ([ xs ]ℕ + [ ys ]ℕ)
    ≡⟨ cong suc (+-*-suc 2 ([ xs ]ℕ + [ ys ]ℕ)) ⟩
        1 + (2 + 2 * ([ xs ]ℕ + [ ys ]ℕ))
    ≡⟨ cong (λ x → 1 + (2 + x)) (distrib-left-*-+ 2 [ xs ]ℕ [ ys ]ℕ) ⟩
        1 + (2 + 2 * [ xs ]ℕ + 2 * [ ys ]ℕ)
    ≡⟨ cong (λ x → 1 + (x + 2 * [ ys ]ℕ)) (+-comm 2 (2 * [ xs ]ℕ)) ⟩
        1 + (2 * [ xs ]ℕ + 2 + 2 * [ ys ]ℕ)
    ≡⟨ cong suc (+-assoc (2 * [ xs ]ℕ) 2 (2 * [ ys ]ℕ)) ⟩
        1 + (2 * [ xs ]ℕ + (2 + (2 * [ ys ]ℕ)))
    ∎
[]ℕ-+B-hom (two ∷ xs) (one ∷ ys) =
    begin
        suc (2 * [ incrB (xs +B ys) ]ℕ)
    ≡⟨ cong (λ x → suc (2 * x)) ([]ℕ-incrB-hom (xs +B ys)) ⟩
        suc (2 * suc [ xs +B ys ]ℕ)
    ≡⟨ cong (λ x → suc (2 * suc x)) ([]ℕ-+B-hom xs ys) ⟩
        suc (2 * suc ([ xs ]ℕ + [ ys ]ℕ))
    ≡⟨ cong suc (+-*-suc 2 ([ xs ]ℕ + [ ys ]ℕ)) ⟩
        suc (2 + 2 * ([ xs ]ℕ + [ ys ]ℕ))
    ≡⟨ cong (λ x → suc (2 + x)) (distrib-left-*-+ 2 [ xs ]ℕ [ ys ]ℕ) ⟩
        suc (2 + 2 * [ xs ]ℕ + 2 * [ ys ]ℕ)
    ≡⟨ cong (λ x → suc (suc x)) (sym (+-suc (2 * [ xs ]ℕ) (2 * [ ys ]ℕ))) ⟩
        suc (suc (2 * [ xs ]ℕ + suc (2 * [ ys ]ℕ)))
    ∎

[]ℕ-+B-hom (two ∷ xs) (two ∷ ys) =
    begin
        2 + (2 * [ incrB (xs +B ys) ]ℕ)
    ≡⟨ cong (λ x → 2 + (2 * x)) ([]ℕ-incrB-hom (xs +B ys)) ⟩
        2 + (2 * suc [ xs +B ys ]ℕ)
    ≡⟨ cong (λ x → 2 + 2 * suc x) ([]ℕ-+B-hom xs ys) ⟩
        2 + (2 * suc ([ xs ]ℕ + [ ys ]ℕ))
    ≡⟨ cong (λ x → 2 + x) (+-*-suc 2 ([ xs ]ℕ + [ ys ]ℕ)) ⟩
        2 + (2 + 2 * ([ xs ]ℕ + [ ys ]ℕ))
    ≡⟨ cong (λ x → 2 + (2 + x)) (distrib-left-*-+ 2 [ xs ]ℕ [ ys ]ℕ) ⟩
        2 + (2 + 2 * [ xs ]ℕ + 2 * [ ys ]ℕ)
    ≡⟨ cong (λ x → 2 + (x + 2 * [ ys ]ℕ)) (+-comm 2 (2 * [ xs ]ℕ)) ⟩
        2 + (2 * [ xs ]ℕ + 2 + 2 * [ ys ]ℕ)
    ≡⟨ cong (λ x → 2 + x) (+-assoc (2 * [ xs ]ℕ) 2 (2 * [ ys ]ℕ)) ⟩
        2 + (2 * [ xs ]ℕ + (2 + 2 * [ ys ]ℕ))
    ∎

[]ℕ-*2-hom : ∀ xs → [ *2 xs ]ℕ ≡ 2 * [ xs ]ℕ
[]ℕ-*2-hom [] = refl
[]ℕ-*2-hom (one ∷ xs) =
    begin
        2 + 2 * [ *2 xs ]ℕ
    ≡⟨ cong (λ x → 2 + 2 * x) ([]ℕ-*2-hom xs) ⟩
        2 + 2 * (2 * [ xs ]ℕ)
    ≡⟨ cong suc (sym (+-suc (2 * [ xs ]ℕ) (2 * [ xs ]ℕ + zero))) ⟩
        suc (2 * [ xs ]ℕ + suc (2 * [ xs ]ℕ + zero))
    ∎
[]ℕ-*2-hom (two ∷ xs) =
    begin
        2 + 2 * [ incrB (*2 xs) ]ℕ
    ≡⟨ cong (λ x → 2 + 2 * x) ([]ℕ-incrB-hom (*2 xs)) ⟩
        2 + 2 * suc [ *2 xs ]ℕ
    ≡⟨ cong (λ x → 2 + 2 * suc x) ([]ℕ-*2-hom xs) ⟩
        2 + 2 * suc (2 * [ xs ]ℕ)
    ≡⟨ cong (λ x → 2 + x) (sym (+-suc (2 * [ xs ]ℕ) (suc (2 * [ xs ]ℕ + zero)))) ⟩
        2 + (2 * [ xs ]ℕ + suc (suc (2 * [ xs ]ℕ + zero)))
    ∎


[[]B]ℕ-id : ∀ n → [ [ n ]B ]ℕ ≡ n
[[]B]ℕ-id zero = refl
[[]B]ℕ-id (suc n) =
    begin
        [ incrB [ n ]B ]ℕ
    ≡⟨ []ℕ-incrB-hom [ n ]B ⟩
        suc [ [ n ]B ]ℕ
    ≡⟨ cong suc ([[]B]ℕ-id n) ⟩
        suc n
    ∎

[]ℕ-kernal : ∀ xs → [ xs ]ℕ ≡ 0 → xs ≡ []
[]ℕ-kernal [] pf = refl
[]ℕ-kernal (one ∷ xs) pf = contradiction pf (λ ())
[]ℕ-kernal (two ∷ xs) pf = contradiction pf (λ ())

[]ℕ-surjective : ∀ (x : ℕ) → ∃ (λ y → [ y ]ℕ ≡ x)
[]ℕ-surjective n = [ n ]B , [[]B]ℕ-id n
{-
[]ℕ-injective : ∀ x y → [ x ]ℕ ≡ [ y ]ℕ → x ≡ y
[]ℕ-injective []       []       pf = refl
[]ℕ-injective []       (y ∷ ys) pf = sym ([]ℕ-kernal (y ∷ ys) (sym pf))
[]ℕ-injective (x ∷ xs) []       pf = []ℕ-kernal (x ∷ xs) pf
[]ℕ-injective (one ∷ xs) (one ∷ ys) pf =
    begin
        one ∷ xs
    ≡⟨ cong (λ x → one ∷ x) ([]ℕ-injective xs ys {!   !}) ⟩
        one ∷ ys
    ∎
    --let pf0 = trans pf (cong (λ x → 1 + 2 * x) {!   !})
    --in {!   !}
[]ℕ-injective (one ∷ xs) (two ∷ ys) pf = {!   !}
[]ℕ-injective (two ∷ xs) (y ∷ ys) pf = {!   !}
-}
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
