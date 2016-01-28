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

-- an arrow that respects indices
_⇒_ : ∀ {I} → (I → Set) → (I → Set) → Set
_⇒_ {I} X Y = (i : I) → X i → Y i

map : ∀ {I} {A B : I → Set} → (D : Desc I) → (A ⇒ B) → ⟦ D ⟧ A ⇒ ⟦ D ⟧ B
map (arg T U) f i (t , u) = t     , map (U t) f i u
map (rec j D) f i (a , u) = f j a , map D     f i u
map (ret j)   f i i≡j     = i≡j

Alg : ∀ {I} (D : Desc I) → (A : I → Set) → Set
Alg D A = ⟦ D ⟧ A ⇒ A

-- fold D alg i ⟨ x ⟩ = alg i (map D (fold D alg) i x)
-- mapFold F G alg i x = map F (fold G alg) i x

mapFold : ∀ {I} {A : I → Set} (F G : Desc I) → Alg G A → ⟦ F ⟧ (Data G) ⇒ ⟦ F ⟧ A
mapFold (arg Tags decoder) G alg i (tag , subnode) = tag , (mapFold (decoder tag) G alg i subnode)
mapFold (rec j F)          G alg i (⟨ x ⟩ , xs) = alg j (mapFold G G alg j x) , mapFold F G alg i xs
mapFold (ret j)            G alg i x = x

fold : ∀ {I} {A : I → Set} (D : Desc I) → Alg D A → Data D ⇒ A
fold D alg i ⟨ x ⟩ = alg i (mapFold D D alg i x)

-- ℕ
ℕDesc : Desc ⊤
ℕDesc = arg Bool (λ { true → rec tt (ret tt) ; false → ret tt })

ℕ : Set
ℕ = Data ℕDesc tt

zero : ℕ
zero = ⟨ (false , refl) ⟩

suc : ℕ → ℕ
suc n = ⟨ (true , (n , refl)) ⟩

-- indℕ : (P : ℕ → Set)
--      → P zero
--      → ((n : ℕ) → P n → P (suc n))
--      → (x : ℕ)
--      → P x
-- indℕ P base step ⟨ true , n , refl ⟩ = step n (indℕ P base step n)
-- indℕ P base step ⟨ false , refl ⟩ = base
--
-- _+_ : ℕ → ℕ → ℕ
-- x + y = indℕ (λ _ → ℕ) y (λ n prf → suc prf) x

+alg : ℕ → Alg ℕDesc (λ _ → ℕ)
+alg y .tt (true , sum , refl) = suc sum
+alg y .tt (false , refl) = y

_+_ : ℕ → ℕ → ℕ
x + y = fold ℕDesc (+alg y) tt x

one : ℕ
one = suc zero

two : ℕ
two = suc one

+-suc-left : (m n : ℕ) → suc m + n ≡ suc (m + n)
+-suc-left ⟨ true , m , refl ⟩ n = refl
+-suc-left ⟨ false , refl ⟩ n = refl

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
consV {A} {n} x xs = ⟨ true , x , n , xs , refl ⟩

++alg : ∀ {A n} → Vec A n → Alg (VecDesc A) (λ m → Vec A (m + n))
++alg {A} {n} ys .(suc o) (true , z , o , zs , refl) = ⟨ true , z , o + n , zs , sym (+-suc-left o n) ⟩
++alg ys .zero    (false , refl) = ys

_++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
_++_ {A} {m} {n} xs ys = fold (VecDesc A) (++alg ys) m xs

data Inv {J I : Set} (e : J → I) : I → Set where
    inv : (j : J) → Inv e (e j)

data Orn {J I : Set} (e : J → I) : Desc I → Set₁ where
    arg : (A : Set) → {D : A → Desc I} → ((a : A) → Orn e (D a)) → Orn e (Desc.arg A D)
    rec : ∀ {h D} → Inv e h → Orn e D → Orn e (rec h D)
    ret : ∀ {o} → Inv e o → Orn e (ret o)
    new : ∀ {D} → (A : Set) → ((a : A) → Orn e D) → Orn e D

ListOrn : Set → Orn (λ x → tt) ℕDesc
ListOrn A = arg Bool (λ { true → Orn.new A (λ a → rec (inv tt) (ret (inv tt)))
                   ; false → Orn.ret (inv tt)})

orn : ∀ {I J} {D : Desc I} {e : J → I} → Orn e D → Desc J
orn (arg A O) = arg A (λ x → orn (O x))
orn (rec (inv j) O) = rec j (orn O)
orn (ret (inv j)) = ret j
orn (new A O) = arg A (λ x → orn (O x))
