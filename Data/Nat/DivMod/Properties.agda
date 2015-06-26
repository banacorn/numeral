module Data.Nat.DivMod.Properties where


open import Data.Nat
open ≤-Reasoning
open import Data.Nat.DivMod
open import Data.Nat.Etc
open import Data.Nat.Properties using (≰⇒>; m≤m+n)
open import Data.Nat.Properties.Simple using (+-right-identity; +-suc; +-assoc; +-comm; distribʳ-*-+)
open import Data.Fin using (Fin; toℕ; fromℕ≤; inject≤)
    renaming (_+_ to _F+_; zero to Fzero; suc to Fsuc)
open import Data.Fin.Properties using (bounded)
open import Function
-- import Level

open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Nullary.Decidable using (True; False; toWitness)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; sym; trans; inspect)
open PropEq.≡-Reasoning
    renaming (begin_ to beginEq_; _≡⟨_⟩_ to _≡Eq⟨_⟩_; _∎ to _∎Eq)

ℕ-isDecTotalOrder   = DecTotalOrder.isDecTotalOrder decTotalOrder
ℕ-isTotalOrder      = IsDecTotalOrder.isTotalOrder ℕ-isDecTotalOrder
ℕ-isPartialOrder    = IsTotalOrder.isPartialOrder ℕ-isTotalOrder
ℕ-isPreorder        = IsPartialOrder.isPreorder ℕ-isPartialOrder
≤-refl      = IsPreorder.reflexive ℕ-isPreorder
≤-antisym   = IsPartialOrder.antisym ℕ-isPartialOrder
≤-total     = IsTotalOrder.total ℕ-isTotalOrder

lem-+-exchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
lem-+-exchange a b c d = beginEq
        (a + b) + (c + d)
    ≡Eq⟨ sym (+-assoc (a + b) c d) ⟩
        a + b + c + d
    ≡Eq⟨ cong (λ x → x + d) (+-assoc a b c) ⟩
        a + (b + c) + d
    ≡Eq⟨ cong (λ x → a + x + d) (+-comm b c) ⟩
        a + (c + b) + d
    ≡Eq⟨ cong (λ x → x + d) (sym (+-assoc a c b)) ⟩
        a + c + b + d
    ≡Eq⟨ +-assoc (a + c) b d ⟩
        (a + c) + (b + d)
    ∎Eq

_DivMod+_ : ∀ {b m n} → DivMod m b → DivMod n b → DivMod (m + n) b
_DivMod+_ {zero}          (result q₀ () prop₀) (result q₁ () prop₁)
_DivMod+_ {suc b}         (result q₀ r₀ prop₀) (result q₁ r₁ prop₁) with ((toℕ r₀ + toℕ r₁) divMod (suc b))
_DivMod+_ {suc b} {m} {n} (result q₀ r₀ prop₀) (result q₁ r₁ prop₁) | result zero rᵣ propᵣ =
    let q = q₀ + q₁
        r = rᵣ
    in  result q r $
            beginEq
                m + n
            ≡Eq⟨ cong₂ _+_ prop₀ prop₁ ⟩
                (toℕ r₀ + q₀ * suc b) + (toℕ r₁ + q₁ * suc b)
            ≡Eq⟨ lem-+-exchange (toℕ r₀) (q₀ * suc b) (toℕ r₁) (q₁ * suc b) ⟩
                toℕ r₀ + toℕ r₁ + (q₀ * suc b + q₁ * suc b)
            ≡Eq⟨ cong₂ _+_ propᵣ (sym (distribʳ-*-+ (suc b) q₀ q₁)) ⟩
                toℕ rᵣ + zero + q * suc b
            ≡Eq⟨ cong (λ x → x + q * suc b) (+-right-identity (toℕ rᵣ)) ⟩
                toℕ r + q * suc b
            ∎Eq
_DivMod+_ {suc b} {m} {n} (result q₀ r₀ prop₀) (result q₁ r₁ prop₁) | result (suc qᵣ) rᵣ propᵣ =
    let q = q₀ + q₁ + suc qᵣ
        r = rᵣ
    in  result q r $
            beginEq
                m + n
            ≡Eq⟨ cong₂ _+_ prop₀ prop₁ ⟩
                (toℕ r₀ + q₀ * suc b) + (toℕ r₁ + q₁ * suc b)
            ≡Eq⟨ lem-+-exchange (toℕ r₀) (q₀ * suc b) (toℕ r₁) (q₁ * suc b) ⟩
                (toℕ r₀ + toℕ r₁) + (q₀ * suc b + q₁ * suc b)
            ≡Eq⟨ cong₂ _+_ propᵣ (sym (distribʳ-*-+ (suc b) q₀ q₁)) ⟩
                toℕ rᵣ + suc qᵣ * suc b + (q₀ + q₁) * suc b
            ≡Eq⟨ +-assoc (toℕ rᵣ) (suc qᵣ * suc b) ((q₀ + q₁) * suc b) ⟩
                toℕ rᵣ + (suc qᵣ * suc b + (q₀ + q₁) * suc b)
            ≡Eq⟨ cong (λ x → toℕ rᵣ + x) (sym (distribʳ-*-+ (suc b) (suc qᵣ) (q₀ + q₁))) ⟩
                toℕ rᵣ + (suc qᵣ + (q₀ + q₁)) * suc b
            ≡Eq⟨ cong (λ x → toℕ rᵣ + x * suc b) (+-comm (suc qᵣ) (q₀ + q₁)) ⟩
                toℕ rᵣ + (q₀ + q₁ + suc qᵣ) * suc b
            ∎Eq

{-
DivMod+-left-identity : ∀ {b m} → (x : DivMod m (suc b)) → (result 0 Fzero refl) DivMod+ x ≡ x
DivMod+-left-identity {b} {m} (result q r prop) with (toℕ Fzero + toℕ r) divMod (suc b)
DivMod+-left-identity {b} {m} (result q r prop) | result zero rᵣ propᵣ =
    -- propᵣ : toℕ r ≡ toℕ rᵣ + 0
    -- prop  :      m ≡ toℕ r  + q * suc b
    -- prop  :      m ≡ toℕ rᵣ + q * suc b
    -- trans (cong₂ _+_ refl prop) (trans (trans (cong (λ z → z + q * suc b) (sym (+-right-identity (toℕ r)))) (trans (+-assoc (toℕ r) zero (q * suc b)) refl)) (trans (cong₂ _+_ propᵣ refl) (trans (cong (λ z → z + q * suc b) (+-right-identity (toℕ rᵣ))) refl))))
    let prop' = beginEq
                m
            ≡Eq⟨ cong₂ _+_ refl prop ⟩
                toℕ r + q * suc b
            ≡Eq⟨ cong₂ _+_ propᵣ refl ⟩
                toℕ rᵣ + 0 + q * suc b
            ≡Eq⟨ cong₂ _+_ (+-right-identity (toℕ rᵣ)) refl ⟩
                toℕ rᵣ + q * suc b
            ∎Eq
    in  beginEq
            result q rᵣ prop'
        ≡Eq⟨ cong (λ x → result q x {! prop'  !}) (sym {! +-right-identity  !}) ⟩
            {!   !}
        ≡Eq⟨ {!   !} ⟩
            {!   !}
        ≡Eq⟨ {!   !} ⟩
            {!   !}
        ≡Eq⟨ {!   !} ⟩
            result q r prop
        ∎Eq
DivMod+-left-identity (result q r prop) | result (suc qᵣ) rᵣ propᵣ = {!   !}
-}
{-
DivMod+-left-identity : ∀ {b m} → (x : DivMod m (suc b)) → (result 0 Fzero refl) DivMod+ x ≡ x
DivMod+-left-identity {b} {m} (result q r prop) with (toℕ r) divMod (suc b)
DivMod+-left-identity {b} {m} (result q r prop) | result zero rᵣ propᵣ =
    beginEq
        result q rᵣ (beginEq
                m
            ≡Eq⟨ cong (λ z → z) prop ⟩
                toℕ r + q * suc b
            ≡Eq⟨ cong (λ z → z + q * suc b) (sym (+-right-identity (toℕ r))) ⟩
                (toℕ r + zero) + q * suc b
            ≡Eq⟨ cong (λ z → z + zero + q * suc b) propᵣ ⟩
                toℕ rᵣ + zero + zero + q * suc b
            ≡Eq⟨ cong (λ z → z + zero + q * suc b) (+-right-identity (toℕ rᵣ)) ⟩
                (toℕ rᵣ + zero) + q * suc b
            ≡Eq⟨ +-assoc (toℕ rᵣ) zero (q * suc b) ⟩
                toℕ rᵣ + q * suc b
            ∎Eq)
    ≡Eq⟨ {!   !} ⟩
        result q r prop
    ∎Eq
DivMod+-left-identity (result q r prop) | result (suc qᵣ) rᵣ propᵣ =
    beginEq
        (result 0 Fzero refl) DivMod+ {!   !}
    ≡Eq⟨ {!   !} ⟩
        {!   !}
    ≡Eq⟨ {!    !} ⟩
        {!    !}
    ≡Eq⟨ {!    !} ⟩
        result q r prop
    ∎Eq

DivMod+-left-identity : (b n : ℕ) → (≢0 : False (b ≟ 0)) → ((0 divMod b) {≢0}) DivMod+ ((n divMod b) {≢0}) ≡ ((n divMod b) {≢0})
DivMod+-left-identity zero n ()
DivMod+-left-identity (suc b) zero ≢0 = refl
DivMod+-left-identity (suc b) (suc n) ≢0 = {!   !}

divMod-hom : (b m n : ℕ) → (≢0 : False (b ≟ 0)) → ((m + n) divMod b) {≢0} ≡ ((m divMod b) {≢0}) DivMod+ ((n divMod b) {≢0})
divMod-hom zero    m n ()
divMod-hom (suc b) zero n ≢0 = {!   !}
divMod-hom (suc b) (suc m) n ≢0  = {!   !}

div-suc-mono : (n base : ℕ)  → (≢0 : False (base ≟ 0))
             → let _/base = λ x → (x div base) {≢0}
               in suc n /base ≥ n /base
div-suc-mono n       zero    ()
div-suc-mono zero    (suc b) ≢0 = z≤n
div-suc-mono (suc n) (suc b) ≢0 = {!   !}

-}

--  TODO: proof div monotone
postulate
    div-mono : (base : ℕ) → (≢0 : False (base ≟ 0))
             → let _/base = λ x → (x div base) {≢0}
               in  _/base Preserves _≤_ ⟶ _≤_

n/n≡1 : ∀ n → (≢0 : False (n ≟ 0)) → (n div n) {≢0} ≡ 1
n/n≡1 zero ()
n/n≡1 (suc n) ≢0 with ((suc n) divMod (suc n)) {≢0} | inspect (λ w → ((suc n) divMod (suc n)) {w}) ≢0
n/n≡1 (suc n) ≢0 | result zero r prop | PropEq.[ eq ] =
    let prop' : suc n ≡ toℕ r
        prop' = trans prop (+-right-identity (toℕ r))
    in  contradiction (≤-refl prop') (>⇒≰ (bounded r))
n/n≡1 (suc n) ≢0 | result (suc zero) r prop | PropEq.[ eq ] = {!   !}
n/n≡1 (suc n) ≢0 | result (suc (suc q)) r prop | PropEq.[ eq ] =
    let prop' : suc n ≡ suc n + toℕ r + suc q * suc n
        prop' = beginEq
                suc n
            ≡Eq⟨ prop ⟩
                toℕ r + (suc n + suc (n + q * suc n))
            ≡Eq⟨ sym (+-assoc (toℕ r) (suc n) (suc (n + q * suc n))) ⟩
                toℕ r + suc n + suc (n + q * suc n)
            ≡Eq⟨ cong₂ _+_ (+-comm (toℕ r) (suc n)) refl ⟩
                suc (n + toℕ r + suc (n + q * suc n))
            ∎Eq
    in  contradiction (≤-refl prop') (>⇒≰ {!   !})

lem : ∀ m n → n ≤ m → (≢0 : False (n ≟ 0)) → (n div n) {≢0} ≤ (m div n) {≢0}
lem m zero n≤m ()
lem m (suc n) n≤m ≢0 = div-mono (suc n) {!   !} n≤m

{-
div-mono : (base : ℕ) → (≢0 : False (base ≟ 0))
         → let _/base = λ x → (x div base) {≢0}
           in  _/base Preserves _≤_ ⟶ _≤_
div-mono zero () rel
div-mono (suc b) ≢0 z≤n = z≤n
div-mono (suc b) ≢0 (s≤s {x} {y} rel) with compare x y
div-mono (suc b) ≢0 (s≤s rel) | less m k with ((suc m) divMod (suc b)) {≢0}
                                            | inspect (λ w → ((suc m) divMod (suc b)) {w}) ≢0
                                            | ((suc (suc m + k)) divMod (suc b)) {≢0}
                                            | inspect (λ w → ((suc (suc m + k)) divMod (suc b)) {w}) ≢0
                                            | ((suc k) divMod (suc b)) {≢0}
                                            | inspect (λ w → ((suc k) divMod (suc b)) {w}) ≢0
div-mono (suc b) ≢0 (s≤s rel) | less m k | result q₀ r₀ prop₀ | PropEq.[ eq₀ ] | result q₁ r₁ prop₁ | PropEq.[ eq₁ ] | result q₂ r₂ prop₂ | PropEq.[ eq₂ ] =
    -- prop₀:      suc m      ≡ toℕ r₀ + qₒ * suc b
    -- prop₁: suc (suc m + k) ≡ toℕ r₁ + q₁ * suc b
    -- prop₂: suc          k  ≡ toℕ r₂ + q₂ * suc b
    begin
        q₀
    ≤⟨ {!   !} ⟩
        {!    !}
    ≤⟨ {!    !} ⟩
        {!    !}
    ≤⟨ {!    !} ⟩
        {!    !}
    ≤⟨ {!    !} ⟩
        {!    !}
    ≤⟨ {!    !} ⟩
        {!    !}
    ≤⟨ {!    !} ⟩
        q₁
    ∎
div-mono (suc b) ≢0 (s≤s rel) | equal m = ≤-refl refl
div-mono (suc b) ≢0 (s≤s rel) | greater m k = contradiction rel (>⇒≰ (s≤s (m≤m+n m k)))



div-mono (suc b) ≢0 (s≤s {x} {y} rel)   with (x divMod (suc b)) {≢0}
                                        | inspect (λ w → (x divMod (suc b)) {w}) ≢0
                                        | (y divMod (suc b)) {≢0}
                                        | inspect (λ w → (y divMod (suc b)) {w}) ≢0
div-mono (suc b) ≢0 (s≤s {x} {y} rel)   | result qx rx propx | PropEq.[ eqx ] | result qy ry propy | PropEq.[ eqy ] with  = {!   !}


    begin
        {!   !}
    <⟨ {!   !} ⟩
        {!   !}
    <⟨ {!   !} ⟩
        {!   !}
    ∎

    begin
        {!   !}
    ≤⟨ {!    !} ⟩
        {!    !}
    ≤⟨ {!    !} ⟩
        {!   !}
    ≤⟨ {!    !} ⟩
        {!   !}
    ≤⟨ {!    !} ⟩
        {!   !}
    ∎
    beginEq
        {!   !}
    ≡Eq⟨ {!   !} ⟩
        {!   !}
    ≡Eq⟨ {!   !} ⟩
        {!   !}
    ≡Eq⟨ {!   !} ⟩
        {!   !}
    ≡Eq⟨ {!   !} ⟩
        {!   !}
    ∎Eq
-}
