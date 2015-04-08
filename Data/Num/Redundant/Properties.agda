module Data.Num.Redundant.Properties where

open import Data.Num.Nat
open import Data.Num.Redundant renaming (_+_ to _+R_)

open import Data.Nat
open import Data.Nat.Etc
open import Data.Nat.Properties.Simple

open import Data.Sum
open import Data.List hiding ([_])
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; cong₂; trans; sym; inspect)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------
--  Digits
--------------------------------------------------------------------------------

⊕-comm : (a b : Digit) → a ⊕ b ≡ b ⊕ a
⊕-comm zero zero = refl
⊕-comm zero one = refl
⊕-comm zero two = refl
⊕-comm one zero = refl
⊕-comm one one = refl
⊕-comm one two = refl
⊕-comm two zero = refl
⊕-comm two one = refl
⊕-comm two two = refl

⊕-assoc : (a b c : Digit) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
⊕-assoc zero b c = refl
⊕-assoc one zero c = refl
⊕-assoc one one zero = refl
⊕-assoc one one one = refl
⊕-assoc one one two = refl
⊕-assoc one two zero = refl
⊕-assoc one two one = refl
⊕-assoc one two two = refl
⊕-assoc two zero c = refl
⊕-assoc two one zero = refl
⊕-assoc two one one = refl
⊕-assoc two one two = refl
⊕-assoc two two zero = refl
⊕-assoc two two one = refl
⊕-assoc two two two = refl

⊕-right-identity : (a : Digit) → a ⊕ zero ≡ a
⊕-right-identity zero = refl
⊕-right-identity one = refl
⊕-right-identity two = refl

⊙-comm : (a b : Digit) → a ⊙ b ≡ b ⊙ a
⊙-comm zero zero = refl
⊙-comm zero one = refl
⊙-comm zero two = refl
⊙-comm one zero = refl
⊙-comm one one = refl
⊙-comm one two = refl
⊙-comm two zero = refl
⊙-comm two one = refl
⊙-comm two two = refl

--------------------------------------------------------------------------------
--  Sequence of Digits
--------------------------------------------------------------------------------

[x∷xs≡0⇒xs≡0] : (d : Digit) → (xs : Redundant) → [ d ∷ xs ] ≡ [ zero ∷ [] ] → [ xs ] ≡ [ zero ∷ [] ]
[x∷xs≡0⇒xs≡0] d    []       _ = refl
[x∷xs≡0⇒xs≡0] zero (x ∷ xs) p = no-zero-divisor 2 ([ x ] + 2 * [ xs ]) (λ ()) p
[x∷xs≡0⇒xs≡0] one  (x ∷ xs) p = contradiction p (λ ())
[x∷xs≡0⇒xs≡0] two  (x ∷ xs) p = contradiction p (λ ())

[>>xs]≡2*[xs] : (xs : Redundant) → [ >> xs ] ≡ 2 * [ xs ]
[>>xs]≡2*[xs] xs = refl

[n>>>xs]≡2^n*[xs] : (n : ℕ) → (xs : Redundant) → [ n >>> xs ] ≡ 2 ^ n * [ xs ]
[n>>>xs]≡2^n*[xs] zero    xs = sym (+-right-identity [ xs ])
[n>>>xs]≡2^n*[xs] (suc n) xs =
    begin
        [ n >>> (zero ∷ xs) ]
    ≡⟨ [n>>>xs]≡2^n*[xs] n (zero ∷ xs) ⟩
        2 ^ n * [ zero ∷ xs ]
    ≡⟨ sym (*-assoc (2 ^ n) 2 [ xs ]) ⟩
        2 ^ n * 2 * [ xs ]
    ≡⟨ cong (λ x → x * [ xs ]) (*-comm (2 ^ n) 2) ⟩
        2 * 2 ^ n * [ xs ]
    ∎

-- >> 0 ≈ 0
>>-zero : (xs : Redundant) → xs ≈ zero ∷ [] → >> xs ≈ zero ∷ []
>>-zero []       _           = eq refl
>>-zero (x ∷ xs) (eq x∷xs≈0) = eq (begin
        2 * [ x ∷ xs ]
    ≡⟨ cong (λ w → 2 * w) x∷xs≈0 ⟩
        2 * 0
    ≡⟨ *-right-zero 2 ⟩
        0
    ∎)

-- << 0 ≈ 0
<<-zero : (xs : Redundant) → xs ≈ zero ∷ [] → << xs ≈ zero ∷ []
<<-zero []       _           = eq refl
<<-zero (x ∷ xs) (eq x∷xs≡0) = eq ([x∷xs≡0⇒xs≡0] x xs x∷xs≡0)

>>>-zero : ∀ {n} (xs : Redundant) → {xs≈0 : xs ≈ zero ∷ []} → n >>> xs ≈ zero ∷ []
>>>-zero {n} xs {eq xs≡0} = eq (
    begin
        [ n >>> xs ]
    ≡⟨ [n>>>xs]≡2^n*[xs] n xs ⟩
        2 ^ n * [ xs ]
    ≡⟨ cong (λ x → 2 ^ n * x) xs≡0 ⟩
        2 ^ n * 0
    ≡⟨ *-right-zero (2 ^ n) ⟩
        0
    ∎)

<<<-zero : (n : ℕ) (xs : Redundant) → {xs≈0 : xs ≈ zero ∷ []} → n <<< xs ≈ zero ∷ []
<<<-zero zero    [] = eq refl
<<<-zero (suc n) [] = eq refl
<<<-zero zero    (x ∷ xs) {x∷xs≈0}    = x∷xs≈0
<<<-zero (suc n) (x ∷ xs) {eq x∷xs≡0} = <<<-zero n xs {eq ([x∷xs≡0⇒xs≡0] x xs x∷xs≡0)}

--------------------------------------------------------------------------------
--  Properties of the relations on Redundant
--------------------------------------------------------------------------------

≈-Setoid : Setoid _ _
≈-Setoid = record
    {   Carrier = Redundant
    ;   _≈_ = _≈_
    ;   isEquivalence = record
        {   refl = ≈-refl
        ;   sym = ≈-sym
        ;   trans = ≈-trans
        }
    }
    where
        ≈-refl : Reflexive _≈_
        ≈-refl = eq refl

        ≈-sym : Symmetric _≈_
        ≈-sym (eq a≈b) = eq (sym a≈b)

        ≈-trans : Transitive _≈_
        ≈-trans (eq a≈b) (eq b≈c) = eq (trans a≈b b≈c)

private
    ℕ-isDecTotalOrder = DecTotalOrder.isDecTotalOrder decTotalOrder
    ℕ-isTotalOrder = IsDecTotalOrder.isTotalOrder ℕ-isDecTotalOrder
    ℕ-total = IsTotalOrder.total ℕ-isTotalOrder
    ℕ-isPartialOrder = IsTotalOrder.isPartialOrder ℕ-isTotalOrder
    ℕ-antisym =  IsPartialOrder.antisym ℕ-isPartialOrder
    ℕ-isPreorder = IsPartialOrder.isPreorder ℕ-isPartialOrder
    ℕ-isEquivalence = IsPreorder.isEquivalence ℕ-isPreorder
    ℕ-reflexive = IsPreorder.reflexive ℕ-isPreorder
    ℕ-trans = IsPreorder.trans ℕ-isPreorder

≲-isPreorder : IsPreorder _ _
≲-isPreorder = record
    {   isEquivalence = Setoid.isEquivalence ≈-Setoid
    ;   reflexive     = ≲-refl
    ;   trans         = ≲-trans
    }
    where
        ≲-refl : _≈_ ⇒ _≲_
        ≲-refl (eq [x]≡[y]) = le (ℕ-reflexive [x]≡[y])

        ≲-trans : Transitive _≲_
        ≲-trans (le [a]≤[b]) (le [b]≤[c]) = le (ℕ-trans [a]≤[b] [b]≤[c])

≲-isPartialOrder : IsPartialOrder _ _
≲-isPartialOrder =  record
    {   isPreorder = ≲-isPreorder
    ;   antisym = antisym
    }
    where
        antisym : Antisymmetric _≈_ _≲_
        antisym (le [x]≤[y]) (le [y]≤[x]) = eq (ℕ-antisym [x]≤[y] [y]≤[x])

≲-isTotalOrder : IsTotalOrder _ _
≲-isTotalOrder = record
    {   isPartialOrder = ≲-isPartialOrder
    ;   total = total
    }
    where
        total : Total _≲_
        total x y with ℕ-total [ x ] [ y ]
        total x y | inj₁ [x]≤[y] = inj₁ (le [x]≤[y])
        total x y | inj₂ [y]≤[x] = inj₂ (le [y]≤[x])

≲-isDecTotalOrder : IsDecTotalOrder _ _
≲-isDecTotalOrder = record
    {   isTotalOrder = ≲-isTotalOrder
    ;   _≟_ = _≈?_
    ;   _≤?_ = _≲?_
    }

≲-decTotalOrder : DecTotalOrder _ _ _
≲-decTotalOrder = record
    {   Carrier = Redundant
    ;   _≈_ = _≈_
    ;   _≤_ = _≲_
    ;   isDecTotalOrder = ≲-isDecTotalOrder
    }
    where
        antisym : Antisymmetric _≈_ _≲_
        antisym (le [x]≤[y]) (le [y]≤[x]) = eq (ℕ-antisym [x]≤[y] [y]≤[x])


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
