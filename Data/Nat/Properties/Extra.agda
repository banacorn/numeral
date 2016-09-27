module Data.Nat.Properties.Extra where

open import Data.Nat
open import Data.Product
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Function
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Nullary.Negation
open import Relation.Nullary
-- open import Relation.Nullary.Decidable
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

≤-trans :  Transitive _≤_
≤-trans = IsPreorder.trans isPreorder

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

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m n =
    start
        m
    ≤⟨ m≤m+n m n ⟩
        m + n
    ≤⟨ reflexive (+-comm m n) ⟩
        n + m
    □

n+-mono-inverse : ∀ n → ∀ {a b} → n + a ≤ n + b → a ≤ b
n+-mono-inverse zero    a≤b       = a≤b
n+-mono-inverse (suc n) (s≤s a≤b) = n+-mono-inverse n a≤b

n+-mono : ∀ n → (λ x → n + x) Preserves _≤_ ⟶ _≤_
n+-mono n = _+-mono_ {n} {n} ≤-refl

+n-mono : ∀ n → (λ x → x + n) Preserves _≤_ ⟶ _≤_
+n-mono n {a} {b} a≤b = _+-mono_ {a} {b} {n} {n} a≤b ≤-refl

+-comm-mono : ∀ {a b c d} → a + b ≤ c + d → b + a ≤ d + c
+-comm-mono {a} {b} {c} {d} p =
    start
        b + a
    ≤⟨ reflexive (+-comm b a) ⟩
        a + b
    ≤⟨ p ⟩
        c + d
    ≤⟨ reflexive (+-comm c d) ⟩
        d + c
    □

+n-mono-inverse :  ∀ n → ∀ {a b} → a + n ≤ b + n → a ≤ b
+n-mono-inverse zero    {a} {b} p = +-comm-mono {a} {0} {b} {0} p
+n-mono-inverse (suc n) {a} {b} p = +n-mono-inverse n p'
    where   p' : a + n ≤ b + n
            p' = ≤-pred $ start
                    suc (a + n)
                ≤⟨ reflexive (sym (+-suc a n)) ⟩
                    a + suc n
                ≤⟨ p ⟩
                    b + suc n
                ≤⟨ reflexive (+-suc b n) ⟩
                    suc (b + n)
                □

+-mono-contra : ∀ {a b c d} → a ≥ b → a + c < b + d → c < d
+-mono-contra {zero} {zero} p q = q
+-mono-contra {zero} {suc b} () q
+-mono-contra {suc a} {zero} {c} {d} p q =
    start
        suc c
    ≤⟨ m≤n+m (suc c) (suc a) ⟩
        suc a + suc c
    ≤⟨ reflexive (+-suc (suc a) c) ⟩
        suc (suc a) + c
    ≤⟨ q ⟩
        d
    □
-- induction
+-mono-contra {suc a} {suc b} (s≤s p) (s≤s q) = +-mono-contra p q

n*-mono : ∀ n → (λ x → n * x) Preserves _≤_ ⟶ _≤_
n*-mono n = _*-mono_ {n} {n} ≤-refl

-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- □

n*-mono-strict-inverse : ∀ n {a} {b} → n * a < n * b → a < b
n*-mono-strict-inverse zero                    ()
n*-mono-strict-inverse (suc n) {zero}  {zero}  p       = n*-mono-strict-inverse n p
n*-mono-strict-inverse (suc n) {zero}  {suc b} (s≤s p) = s≤s z≤n
n*-mono-strict-inverse (suc n) {suc a} {zero}  p       = contradiction p' (λ ())
    where   p' : suc (a + n * suc a) < 0
            p' = start
                    suc (suc (a + n * suc a))
                ≤⟨ p ⟩
                    n * zero
                ≤⟨ reflexive (*-right-zero n) ⟩
                    zero
                □
n*-mono-strict-inverse (suc n) {suc a} {suc b} (s≤s p) with suc a ≤? b
n*-mono-strict-inverse (suc n) {suc a} {suc b} (s≤s p) | yes q = s≤s q
n*-mono-strict-inverse (suc n) {suc a} {suc b} (s≤s p) | no ¬q = contradiction p ¬p
    where   ¬q' : suc b ≤ suc a
            ¬q' = ≰⇒> ¬q
            ¬p : suc (a + n * suc a) ≰ b + n * suc b
            ¬p = >⇒≰ $ n*-mono (suc n) ¬q'

*n-mono : ∀ n → (λ x → x * n) Preserves _≤_ ⟶ _≤_
*n-mono n {a} {b} a≤b = _*-mono_ {a} {b} {n} {n} a≤b ≤-refl

*-comm-mono : ∀ {a b c d} → a * b ≤ c * d → b * a ≤ d * c
*-comm-mono {a} {b} {c} {d} p =
    start
        b * a
    ≤⟨ reflexive (*-comm b a) ⟩
        a * b
    ≤⟨ p ⟩
        c * d
    ≤⟨ reflexive (*-comm c d) ⟩
        d * c
    □

*-comm-mono-strict : ∀ {a b c d} → a * b < c * d → b * a < d * c
*-comm-mono-strict {a} {b} {c} {d} p =
    start
        suc (b * a)
    ≤⟨ reflexive (cong suc (*-comm b a)) ⟩
        suc (a * b)
    ≤⟨ p ⟩
        c * d
    ≤⟨ reflexive (*-comm c d) ⟩
        d * c
    □


*n-mono-inverse : ∀ n {a} {b} → a * (suc n) ≤ b * (suc n) → a ≤ b
*n-mono-inverse n {zero}          p       = z≤n
*n-mono-inverse n {suc a} {zero}  ()
*n-mono-inverse n {suc a} {suc b} (s≤s p) = s≤s (*n-mono-inverse n (n+-mono-inverse n p))

*n-mono-inverse-strict : ∀ n {a} {b} → a * n < b * n → a < b
*n-mono-inverse-strict zero {a} {b} p = contradiction (start
        1
    ≤⟨ reflexive (cong suc (sym (*-right-zero a))) ⟩
        suc (a * zero)
    ≤⟨ p ⟩
        b * zero
    ≤⟨ reflexive (*-right-zero b) ⟩
        0
    □) (λ ())
*n-mono-inverse-strict (suc n) {a} {b} p = *n-mono-inverse-strict n {!   !}
    where
            temp : a + n * a < b + n * b
            temp =
                start
                    suc (a + n * a)
                ≤⟨ reflexive (cong suc (*-comm (suc n) a)) ⟩
                    suc (a * suc n)
                ≤⟨ p ⟩
                    b * suc n
                ≤⟨ reflexive (*-comm b (suc n)) ⟩
                    b + n * b
                □
            temp' : suc n * a < suc n * b
            temp' = *-comm-mono-strict {a} {suc n} {b} p

            temp'' : n * a < n * b
            temp'' = {!   !}

-- *n-mono-inverse-strict (suc n) {zero} {zero} p = p
-- *n-mono-inverse-strict (suc n) {zero} {suc j} (s≤s p) = s≤s z≤n
-- *n-mono-inverse-strict (suc n) {suc i} {zero} ()
-- *n-mono-inverse-strict (suc n) {suc i} {suc j} (s≤s p) = s≤s $
--     start
--         suc i
--     ≤⟨ {!   !} ⟩
--         {!   !}
--     ≤⟨ {!*n-mono-inverse-strict (suc n) {suc i} {suc j} (s≤s p)   !} ⟩
--         {!   !}
--     ≤⟨ {!   !} ⟩
--         j
--     □




≤-suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
≤-suc z≤n = s≤s z≤n
≤-suc (s≤s rel) = s≤s (s≤s rel)

i*j>0⇒i>0∧j>0 : ∀ i j → i * j > 0 → (i > 0 × j > 0)
i*j>0⇒i>0∧j>0 zero j ()
i*j>0⇒i>0∧j>0 (suc i) zero p = contradiction (proj₂ (i*j>0⇒i>0∧j>0 i 0 p)) (λ ())
i*j>0⇒i>0∧j>0 (suc i) (suc j) p = s≤s z≤n , s≤s z≤n

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



-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- □

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
