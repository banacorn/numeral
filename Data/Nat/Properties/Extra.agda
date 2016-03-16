module Data.Nat.Properties.Extra where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Function
open import Relation.Binary.Core
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


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


suc-injective : ∀ {x y} → suc x ≡ suc y → x ≡ y
suc-injective {x} {.x} refl = refl

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
