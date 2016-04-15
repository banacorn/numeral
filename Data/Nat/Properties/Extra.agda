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
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

isDecTotalOrder : IsDecTotalOrder {A = ℕ} _≡_ _≤_
isDecTotalOrder = DecTotalOrder.isDecTotalOrder decTotalOrder

isTotalOrder : IsTotalOrder {A = ℕ} _≡_ _≤_
isTotalOrder = IsDecTotalOrder.isTotalOrder isDecTotalOrder

isPartialOrder : IsPartialOrder {A = ℕ} _≡_ _≤_
isPartialOrder = IsTotalOrder.isPartialOrder isTotalOrder

isPreorder : IsPreorder {A = ℕ} _≡_ _≤_
isPreorder = IsPartialOrder.isPreorder isPartialOrder

<-sucs : ∀ {m n} l → m < n → l + m < l + n
<-sucs zero    m<n = m<n
<-sucs (suc l) m<n = s≤s (<-sucs l m<n)

<-preds : ∀ {m n} l → l + m < l + n → m < n
<-preds zero    m<n       = m<n
<-preds (suc l) (s≤s m<n) = <-preds l m<n


≤-trans :  Transitive _≤_
≤-trans = IsPreorder.trans isPreorder

≤-sucs : ∀ {m n} l → m ≤ n → l + m ≤ l + n
≤-sucs {m} {n} l m≤n = _+-mono_ {l} {l} {m} {n} ≤-refl m≤n

≤-preds : ∀ {m n} l → l + m ≤ l + n → m ≤ n
≤-preds zero    m≤n       = m≤n
≤-preds (suc l) (s≤s m≤n) = ≤-preds l m≤n

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

*-right-identity : ∀ n → n * 1 ≡ n
*-right-identity zero = refl
*-right-identity (suc n) = cong suc (*-right-identity n)

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
