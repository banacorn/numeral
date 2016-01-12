module Sandbox.IndRecIndexed where
-- Ornamental Algebras, Algebraic Ornaments, CONOR McBRIDE
-- https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf
-- A Finite Axiomtization of Inductive-Recursion definitions, Peter Dybjer, Anton Setzer
-- http://www.cse.chalmers.se/~peterd/papers/Finite_IR.pdf

open import Data.Product using (_×_; Σ; _,_)
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data Desc (I : Set) : Set₁ where
    arg : (A : Set) → (A → Desc I) → Desc I
    rec : I → Desc I → Desc I
    ret : I → Desc I

⟦_⟧ : ∀ {I} → Desc I → (I → Set) → (I → Set)
⟦ arg A D ⟧ R i = Σ A (λ a → ⟦ D a ⟧ R i)
⟦ rec j D ⟧ R i = R j × ⟦ D ⟧ R i
⟦ ret j   ⟧ R i = j ≡ i

data Data {I} (D : Desc I) : I → Set where
    ⟨_⟩ : ∀ {i} → ⟦ D ⟧ (Data D) i → Data D i


-- ℕ
ℕDesc : Desc ⊤
ℕDesc = arg Bool (λ { true → rec tt (ret tt) ; false → ret tt })

ℕ : Set
ℕ = Data ℕDesc tt

zero : ℕ
zero = ⟨ (false , refl) ⟩

suc : ℕ → ℕ
suc n = ⟨ (true , (n , refl)) ⟩

indℕ : (P : ℕ → Set)
     → P zero
     → ((n : ℕ) → P n → P (suc n))
     → (x : ℕ)
     → P x
indℕ P base step ⟨ true , n , refl ⟩ = step n (indℕ P base step n)
indℕ P base step ⟨ false , refl ⟩ = base

_+_ : ℕ → ℕ → ℕ
x + y = indℕ (λ _ → ℕ) y (λ n prf → suc prf) x

one : ℕ
one = suc zero

two : ℕ
two = suc one

+-left-identity : (n : ℕ) → zero + n ≡ n
+-left-identity n = indℕ (λ x → zero + x ≡ x) refl (λ n₁ _ → refl) n

+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc m n = indℕ (λ x → x + suc n ≡ suc (x + n)) refl (λ _ prf → cong suc prf) m

+-right-identity : (n : ℕ) → n + zero ≡ n
+-right-identity n = indℕ (λ x → x + zero ≡ x) refl (λ _ prf → cong suc prf) n

-- Nat
NatDesc : Desc ℕ
NatDesc = arg Bool (
    λ { true → arg ℕ (λ { n → rec n (ret (suc n)) })
      ; false → ret zero
      })

Nat : ℕ → Set
Nat n = Data NatDesc n

zeroNat : Nat zero
zeroNat = ⟨ (false , refl) ⟩

sucNat : ∀ {n} → Nat n → Nat (suc n)
sucNat {n} x = ⟨ (true , (n , (x , refl))) ⟩

-- Maybe
MaybeDesc : Set → Desc ⊤
MaybeDesc A = arg Bool (λ { true → arg A (λ _ → ret tt) ; false → ret tt })

Maybe : Set → Set
Maybe A = Data (MaybeDesc A) tt

nothing : ∀ {A} → Maybe A
nothing = ⟨ (false , refl) ⟩

just : ∀ {A} → A → Maybe A
just n = ⟨ (true , (n , refl)) ⟩

-- List
ListDesc : Set → Desc ⊤
ListDesc A = arg Bool (
    λ { true  → arg A (λ _ → rec tt (ret tt))
      ; false → ret tt
      })

List : Set → Set
List A = Data (ListDesc A) tt

nil : ∀ {A} → List A
nil = ⟨ (false , refl) ⟩

cons : ∀ {A} → A → List A → List A
cons x xs = ⟨ (true , (x , (xs , refl))) ⟩

indList : ∀ {A} (P : List A → Set)
        → P nil
        → ((x : A) → (xs : List A) → P xs → P (cons x xs))
        → (xs : List A)
        → P xs
indList P base step ⟨ true , x , xs , refl ⟩ = step x xs (indList P base step xs)
indList P base step ⟨ false , refl ⟩ = base

-- Vec
VecDesc : Set → Desc ℕ
VecDesc A = arg Bool (
  λ { true → arg A (λ _ → arg ℕ (λ n → rec n (ret (suc n))))
    ; false → ret zero
    })

Vec : Set → ℕ → Set
Vec A n = Data (VecDesc A) n

nilV : ∀ {A} → Vec A zero
nilV = ⟨ false , refl ⟩

consV : ∀ {A n} → A → Vec A n → Vec A (suc n)
consV {n = n} x xs = ⟨ (true , (x , n , (xs , refl))) ⟩

indVec : ∀ {A n} (P : ∀ {m} → Vec A m → Set)
       → P nilV
       → ((n : ℕ) → (x : A) → (xs : Vec A n) → P xs → P (consV x xs))
       → (xs : Vec A n)
       → P xs
indVec P base step ⟨ true , A , n , xs , refl ⟩ = step n A xs (indVec P base step xs)
indVec P base step ⟨ false , refl ⟩ = base

_++'_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
⟨ true , x , m , xs , refl ⟩ ++' ⟨ true , y , n , ys , refl ⟩ = ⟨ true , x , m + suc n , xs ++' consV y ys , refl ⟩
⟨ true , x , m , xs , refl ⟩ ++' ⟨ false , refl ⟩ = ⟨ true , x , m , xs , sym (+-right-identity (suc m)) ⟩
⟨ false , refl ⟩ ++' ys = ys

_++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
_++_ {A} {m} {n} xs ys = indVec (λ {m} x → Vec A (m + n)) ys (λ m x xs xs++ys → consV x xs++ys) xs
