module Data.Nat.Properties.Extra where

open import Data.Nat
open import Data.Product
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Function
open import Level using ()
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

open import Algebra.Structures
import Algebra.FunctionProperties as P; open P (_≡_ {A = ℕ})

isSemiringWithoutOne : IsSemiringWithoutOne _≡_ _⊔_ _⊓_ zero
isSemiringWithoutOne = IsCommutativeSemiringWithoutOne.isSemiringWithoutOne ⊔-⊓-0-isCommutativeSemiringWithoutOne

+-isCommutativeMonoid : IsCommutativeMonoid _≡_ _⊔_ zero
+-isCommutativeMonoid = IsSemiringWithoutOne.+-isCommutativeMonoid  isSemiringWithoutOne

⊔-comm : Commutative _⊔_
⊔-comm = IsCommutativeMonoid.comm +-isCommutativeMonoid

cmp : Trichotomous _≡_ _<_
cmp = StrictTotalOrder.compare strictTotalOrder

≤-trans : Transitive _≤_
≤-trans = IsPreorder.trans isPreorder

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ {zero} p = z≤n
<⇒≤ {suc i} (s≤s p) = s≤s (<⇒≤ p)

>⇒≰ : _>_ ⇒ _≰_
>⇒≰ {zero}  ()      q
>⇒≰ {suc m} (s≤s p) (s≤s q) = >⇒≰ p q

≤⇒≯ : _≤_ ⇒ _≯_
≤⇒≯ {zero} p ()
≤⇒≯ {suc m} (s≤s p) (s≤s q) = ≤⇒≯ p q

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ {zero} () z≤n
<⇒≱ {suc i} (s≤s p) (s≤s q) = <⇒≱ p q

>⇒≢ : _>_ ⇒ _≢_
>⇒≢ {zero} () refl
>⇒≢ {suc m} (s≤s m>n) refl = >⇒≢ m>n refl

≥⇒≮ : _≥_ ⇒ _≮_
≥⇒≮ z≤n     ()
≥⇒≮ (s≤s m) (s≤s p) = ≥⇒≮ m p

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ {zero} () refl
<⇒≢ {suc m} (s≤s m<n) refl = <⇒≢ m<n refl

≤∧≢⇒< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤∧≢⇒< {zero}  {zero}  p       q = contradiction refl q
≤∧≢⇒< {zero}  {suc n} p       q = s≤s z≤n
≤∧≢⇒< {suc m} {zero}  ()      q
≤∧≢⇒< {suc m} {suc n} (s≤s p) q = s≤s (≤∧≢⇒< p (q ∘ cong suc))

≥∧≢⇒> : ∀ {m n} → m ≥ n → m ≢ n → m > n
≥∧≢⇒> {zero}  {zero}  p       q = contradiction refl q
≥∧≢⇒> {zero}  {suc n} ()      q
≥∧≢⇒> {suc m} {zero}  p       q = s≤s z≤n
≥∧≢⇒> {suc m} {suc n} (s≤s p) q = s≤s (≥∧≢⇒> p (q ∘ cong suc))

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m n =
    start
        m
    ≤⟨ m≤m+n m n ⟩
        m + n
    ≤⟨ reflexive (+-comm m n) ⟩
        n + m
    □

m≡n+o⇒m≥o : ∀ {m} {o} n → m ≡ n + o → m ≥ o
m≡n+o⇒m≥o {.(n + o)} {o} n refl = m≤n+m o n

≤0⇒≡0 : ∀ n → n ≤ 0 → n ≡ 0
≤0⇒≡0 zero    n≤0 = refl
≤0⇒≡0 (suc n) ()

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

∸n-mono : ∀ n → (λ x → x ∸ n) Preserves _≤_ ⟶ _≤_
∸n-mono n {a} {b} a≤b = ∸-mono {a} {b} {n} {n} a≤b ≤-refl

∸n-mono-inverse :  ∀ n → ∀ {a b} → a > n → a ∸ n ≤ b ∸ n → a ≤ b
∸n-mono-inverse zero                    p q = q
∸n-mono-inverse (suc n) {zero}  {zero}  p q = q
∸n-mono-inverse (suc n) {zero}  {suc b} p q = z≤n
∸n-mono-inverse (suc n) {suc a} {zero}  p q = contradiction (≤-pred p) (≤⇒≯ q')
    where
        q' : a ≤ n
        q' = ∸n-mono-inverse n (≤-pred p) $
            start
                a ∸ n
            ≤⟨ q ⟩
                zero
            ≈⟨ sym (n∸n≡0 n) ⟩
                n ∸ n
            □
∸n-mono-inverse (suc n) {suc a} {suc b} p q = s≤s (∸n-mono-inverse n (≤-pred p) q)

n∸-mono : ∀ n → (λ x → n ∸ x) Preserves _≥_ ⟶ _≤_
n∸-mono n {a} {b} a≥b = ∸-mono {n} {n} {a} {b} ≤-refl a≥b

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
n*-mono-strict-inverse zero ()
n*-mono-strict-inverse (suc n) {a} {b} p with suc a ≤? b
n*-mono-strict-inverse (suc n) {a} {b} p | yes q = q
n*-mono-strict-inverse (suc n) {a} {b} p | no ¬q = contradiction p ¬p
    where
        ¬q' : b ≤ a
        ¬q' = ≤-pred (≰⇒> ¬q)
        ¬p : suc (suc n * a) ≰ suc n * b
        ¬p = >⇒≰ (s≤s (n*-mono (suc n) ¬q'))


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

*n-mono-strict-inverse : ∀ n {a} {b} → a * n < b * n → a < b
*n-mono-strict-inverse n {a} {b} p = n*-mono-strict-inverse n (*-comm-mono-strict {a} {n} {b} {n} p)

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

m∸n+n≡m : ∀ {m n} → n ≤ m → m ∸ n + n ≡ m
m∸n+n≡m {m} {n} n≤m =
    begin
        m ∸ n + n
    ≡⟨ +-comm (m ∸ n) n ⟩
        n + (m ∸ n)
    ≡⟨ m+n∸m≡n n≤m ⟩
        m
    ∎


m∸[o∸n]+o≡m+n : ∀ m n o
    → n ≤ o
    → o ∸ n ≤ m
    → m ∸ ( o ∸ n ) + o ≡ m + n
m∸[o∸n]+o≡m+n m n o n≤o o∸n≤m =
    begin
        m ∸ (o ∸ n) + o
    ≡⟨ +-comm (m ∸ (o ∸ n)) o ⟩
        o + (m ∸ (o ∸ n))
    ≡⟨ cong (λ x → x + (m ∸ (o ∸ n))) (sym (m+n∸m≡n {n} {o} n≤o)) ⟩
        (n + (o ∸ n)) + (m ∸ (o ∸ n))
    ≡⟨ +-assoc n (o ∸ n) (m ∸ (o ∸ n)) ⟩
        n + ((o ∸ n) + (m ∸ (o ∸ n)))
    ≡⟨ cong (λ w → n + w) (m+n∸m≡n {o ∸ n} o∸n≤m) ⟩
        n + m
    ≡⟨ +-comm n m ⟩
        m + n
    ∎

m≥n+o⇒m∸o≥n : ∀ m n o → m ≥ n + o → m ∸ o ≥ n
m≥n+o⇒m∸o≥n m n o p =
    start
        n
    ≈⟨ sym (m+n∸n≡m n o) ⟩
        n + o ∸ o
    ≤⟨ ∸-mono {n + o} {m} {o} p ≤-refl ⟩
        m ∸ o
    □

double : ∀ m → m + m ≡ m * 2
double m =
    begin
        m + m
    ≡⟨ cong (λ w → m + w) (sym (+-right-identity m)) ⟩
        m + (m + zero)
    ≡⟨ *-comm (suc (suc zero)) m ⟩
        m * suc (suc zero)
    ∎

m⊔n≤m+n : ∀ m n → m ⊔ n ≤ m + n
m⊔n≤m+n zero n = ≤-refl
m⊔n≤m+n (suc m) zero = s≤s (m≤m+n m zero)
m⊔n≤m+n (suc m) (suc n) = s≤s $
    start
        m ⊔ n
    ≤⟨ m⊔n≤m+n m n ⟩
        m + n
    ≤⟨ n+-mono m (m≤n+m n (suc zero)) ⟩
        m + suc n
    □

cancel-∸-right : ∀ {m n} o → m ≥ o → n ≥ o → m ∸ o ≡ n ∸ o → m ≡ n
cancel-∸-right                 zero    p  q  eq = eq
cancel-∸-right {zero}          (suc o) () q  eq
cancel-∸-right {suc m} {zero}  (suc o) p  () eq
cancel-∸-right {suc m} {suc n} (suc o) p  q  eq = cong suc (cancel-∸-right o (≤-pred p) (≤-pred q) eq)


-- cancel-∸-right : ∀ {m n o} → n ≥ o → m ≡ n ∸ o → m + o ≡ n
-- cancel-∸-right {m} {n} {zero} p eq =
--     begin
--         m + zero
--     ≡⟨ +-right-identity m ⟩
--         m
--     ≡⟨ eq ⟩
--         n
--     ∎
-- cancel-∸-right {m} {zero} {suc o} () eq
-- cancel-∸-right {m} {suc n} {suc o} p eq =
--     begin
--         m + suc o
--     ≡⟨ +-suc m o ⟩
--         suc (m + o)
--     ≡⟨ cong suc (cancel-∸-right {m} {n} {o} (≤-pred p) eq) ⟩
--         suc n
--     ∎
--
-- cancel-∸-right-inverse : ∀ m n o → n ≥ o → m + o ≡ n → m ≡ n ∸ o
-- cancel-∸-right-inverse m n zero p eq =
--     begin
--         m
--     ≡⟨ sym (+-right-identity m) ⟩
--         m + 0
--     ≡⟨ eq ⟩
--         n
--     ∎
-- cancel-∸-right-inverse m zero (suc o) () eq
-- cancel-∸-right-inverse m (suc n) (suc o) p eq =
--     begin
--         m
--     ≡⟨ cancel-∸-right-inverse m n o (≤-pred p) $ cancel-+-left 1 $
--         begin
--             suc m + o
--         ≡⟨ sym (+-suc m o) ⟩
--             m + suc o
--         ≡⟨ eq ⟩
--             suc n
--         ∎
--      ⟩
--         n ∸ o
--     ∎


⊔-upper-bound : ∀ m n o → m + n ≥ o → o ⊔ n ≤ m + n
⊔-upper-bound zero zero zero p = p
⊔-upper-bound zero zero (suc o) ()
⊔-upper-bound zero (suc n) zero p = s≤s (⊔-upper-bound zero n zero z≤n)
⊔-upper-bound zero (suc n) (suc o) p = s≤s (⊔-upper-bound zero n o (≤-pred p))
⊔-upper-bound (suc m) zero zero p = p
⊔-upper-bound (suc m) zero (suc o) p = p
⊔-upper-bound (suc m) (suc n) zero p =
    start
        suc n
    ≤⟨ s≤s (≤-step ≤-refl) ⟩
        suc (suc n)
    ≤⟨ s≤s (m≤n+m (suc n) m) ⟩
        suc (m + suc n)
    □
⊔-upper-bound (suc m) (suc n) (suc o) p =
    start
        suc (o ⊔ n)
    ≤⟨ s≤s (⊔-upper-bound (suc m) n o $
        start
            o
        ≤⟨ ≤-pred p ⟩
            m + suc n
        ≈⟨ +-suc m n ⟩
            suc (m + n)
        □
    ) ⟩
        suc (suc (m + n))
    ≈⟨ cong suc (sym (+-suc m n)) ⟩
        suc (m + suc n)
    □
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
