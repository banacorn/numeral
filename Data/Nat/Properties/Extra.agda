module Data.Nat.Properties.Extra where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Function
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality hiding (isPreorder)
open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)


-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- □


isDecTotalOrder : IsDecTotalOrder {A = ℕ} _≡_ _≤_
isDecTotalOrder = DecTotalOrder.isDecTotalOrder decTotalOrder

isTotalOrder : IsTotalOrder {A = ℕ} _≡_ _≤_
isTotalOrder = IsDecTotalOrder.isTotalOrder isDecTotalOrder

isPartialOrder : IsPartialOrder {A = ℕ} _≡_ _≤_
isPartialOrder = IsTotalOrder.isPartialOrder isTotalOrder

isPreorder : IsPreorder {A = ℕ} _≡_ _≤_
isPreorder = IsPartialOrder.isPreorder isPartialOrder

n+-mono : ∀ n → (λ x → n + x) Preserves _≤_ ⟶ _≤_
n+-mono n = _+-mono_ {n} {n} ≤-refl

+n-mono : ∀ n → (λ x → x + n) Preserves _≤_ ⟶ _≤_
+n-mono n {i} {j} i≤j = _+-mono_ {i} {j} {n} {n} i≤j ≤-refl

n*-mono : ∀ n → (λ x → n * x) Preserves _≤_ ⟶ _≤_
n*-mono n = _*-mono_ {n} {n} ≤-refl

*n-mono : ∀ n → (λ x → x * n) Preserves _≤_ ⟶ _≤_
*n-mono n {i} {j} i≤j = _*-mono_ {i} {j} {n} {n} i≤j ≤-refl

≤-trans :  Transitive _≤_
≤-trans = IsPreorder.trans isPreorder

≤-preds : ∀ {m n} l → l + m ≤ l + n → m ≤ n
≤-preds zero    m≤n       = m≤n
≤-preds (suc l) (s≤s m≤n) = ≤-preds l m≤n

>⇒≰ : _>_ ⇒ _≰_
>⇒≰ {zero}  ()      q
>⇒≰ {suc m} (s≤s p) (s≤s q) = >⇒≰ p q


>⇒≢ : _>_ ⇒ _≢_
>⇒≢ {zero} () refl
>⇒≢ {suc m} (s≤s m>n) refl = >⇒≢ m>n refl

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ {zero} () refl
<⇒≢ {suc m} (s≤s m<n) refl = <⇒≢ m<n refl

≤∧≢⇒< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤∧≢⇒< {zero}  {zero}  p       q = contradiction refl q
≤∧≢⇒< {zero}  {suc n} p       q = s≤s z≤n
≤∧≢⇒< {suc m} {zero}  ()      q
≤∧≢⇒< {suc m} {suc n} (s≤s p) q = s≤s (≤∧≢⇒< p (q ∘ cong suc))

≤0⇒≡0 : ∀ n → n ≤ 0 → n ≡ 0
≤0⇒≡0 zero    n≤0 = refl
≤0⇒≡0 (suc n) ()

≤-suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
≤-suc z≤n = s≤s z≤n
≤-suc (s≤s rel) = s≤s (s≤s rel)

suc-injective : ∀ {x y} → suc x ≡ suc y → x ≡ y
suc-injective {x} {.x} refl = refl

cancel-suc : ∀ {x y} → suc x ≡ suc y → x ≡ y
cancel-suc {x} {.x} refl = refl

+1-injective : ∀ {x y} → x + 1 ≡ y + 1 → x ≡ y
+1-injective {x} {y} p = suc-injective $
    begin
        1 + x
    ≡⟨ +-comm 1 x ⟩
        x + 1
    ≡⟨ p ⟩
        y + 1
    ≡⟨ +-comm y 1 ⟩
        1 + y
    ∎

[a+b]+c≡[a+c]+b : ∀ a b c → a + b + c ≡ a + c + b
[a+b]+c≡[a+c]+b a b c =
    begin
        a + b + c
    ≡⟨ +-assoc a b c ⟩
        a + (b + c)
    ≡⟨ cong (λ x → a + x) (+-comm b c) ⟩
        a + (c + b)
    ≡⟨ sym (+-assoc a c b) ⟩
        a + c + b
    ∎

a+[b+c]≡b+[a+c] : ∀ a b c → a + (b + c) ≡ b + (a + c)
a+[b+c]≡b+[a+c] a b c =
    begin
        a + (b + c)
    ≡⟨ sym (+-assoc a b c) ⟩
        a + b + c
    ≡⟨ cong (λ x → x + c) (+-comm a b) ⟩
        b + a + c
    ≡⟨ +-assoc b a c ⟩
        b + (a + c)
    ∎

*-right-identity : ∀ n → n * 1 ≡ n
*-right-identity zero    = refl
*-right-identity (suc n) = cong suc (*-right-identity n)

*-left-identity : ∀ n → 1 * n ≡ n
*-left-identity zero    = refl
*-left-identity (suc n) = cong suc (*-left-identity n)

m≤m*1+n : ∀ m n → m ≤ m * suc n
m≤m*1+n m zero = reflexive (sym (*-right-identity m))
m≤m*1+n m (suc n) =
    start
        m
    ≤⟨ m≤m+n m (m * suc n) ⟩
        m + m * suc n
    ≤⟨ reflexive (sym (+-*-suc m (suc n))) ⟩
        m * suc (suc n)
    □

cancel-+-right : ∀ k {i j} → i + k ≡ j + k → i ≡ j
cancel-+-right zero {i} {j} p  =
    begin
        i
    ≡⟨ sym (+-right-identity i) ⟩
        i + zero
    ≡⟨ p ⟩
        j + zero
    ≡⟨ +-right-identity j ⟩
        j
    ∎
cancel-+-right (suc k) {i} {j} p = cancel-+-right k lemma
    where   lemma : i + k ≡ j + k
            lemma = suc-injective $
                begin
                    suc (i + k)
                ≡⟨ sym (+-suc i k) ⟩
                    i + suc k
                ≡⟨ p ⟩
                    j + suc k
                ≡⟨ +-suc j k ⟩
                    suc (j + k)
                ∎

distrib-left-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
distrib-left-*-+ m n o =
    begin
        m * (n + o)
    ≡⟨ *-comm m (n + o) ⟩
        (n + o) * m
    ≡⟨ distribʳ-*-+ m n o ⟩
        n * m + o * m
    ≡⟨ cong₂ _+_ (*-comm n m) (*-comm o m) ⟩
        m * n + m * o
    ∎

m∸n+n : ∀ {m n} → n ≤ m → m ∸ n + n ≡ m
m∸n+n {m} {n} n≤m =
    begin
        m ∸ n + n
    ≡⟨ +-comm (m ∸ n) n ⟩
        n + (m ∸ n)
    ≡⟨ m+n∸m≡n n≤m ⟩
        m
    ∎


-- begin
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ∎
