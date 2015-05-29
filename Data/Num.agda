module Data.Num where

open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat as Nat using (ℕ; zero; suc; pred; s≤s; z≤n; ≤-pred; decTotalOrder; _≟_
    ;   compare
    )
    renaming (_+_ to _N+_; _∸_ to _N-_;
              _*_ to _N*_;
              _<_ to _N<_; _≤_ to _N≤_; _≤?_ to _N≤?_; _>_ to _N>_)
open Nat.≤-Reasoning

open import Data.Nat.DivMod
open import Data.Nat.Properties using (m≤m+n; _+-mono_)
open import Data.Nat.Properties.Simple using (+-right-identity; +-suc; +-assoc; +-comm)
open import Data.Fin.Properties using (bounded)
open import Data.Fin using (Fin; inject₁; fromℕ≤)
    renaming (toℕ to Fin⇒ℕ; fromℕ to ℕ⇒Fin; zero to Fz; suc to Fs)
open import Data.Product

open import Function
open import Data.Unit using (tt)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (False)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary

open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; sym; trans; inspect)

-- Surjective (ℕm):
--  base = 1, digits = {m ... (m + n) - 1}, m ≥ 1, n ≥ m
--  base > 1, digits = {m ... (m + n) - 1}, m ≥ 0, n ≥ max base (base × m)
-- Bijective:
--  base ≥ 1, digits = {1 .. base}
--
--  Digits:
--    Digit m n represents a Digit ranging from m to (m + n - 1)
--    e.g. Digit 2 0 2 = {0, 1}         for ordinary binary number
--         Digit 2 1 2 = {1, 2}         for zeroless binary number
--         Digit 2 0 3 = {0, 1, 2}      for redundant binary number
--

data Digit : (base from range : ℕ) → Set where
    D1 : ∀ {  m n}
         → Fin n
         → {m≤n : m N≤ n}
         → Digit 1 m n
    Dn : ∀ {b m n}
         → Fin n
         → let base = suc (suc b) in
           {b≤n : base N≤ n} → {bm≤n : (base N* m) N≤ n}
         → Digit base m n

Digit⇒ℕ : ∀ {b m n} → Digit b m n → ℕ
Digit⇒ℕ {m = m} (D1 x) = m N+ Fin⇒ℕ x
Digit⇒ℕ {m = m} (Dn x) = m N+ Fin⇒ℕ x

-- alias
ℕ-isDecTotalOrder   = DecTotalOrder.isDecTotalOrder decTotalOrder
ℕ-isTotalOrder      = IsDecTotalOrder.isTotalOrder ℕ-isDecTotalOrder
ℕ-isPartialOrder    = IsTotalOrder.isPartialOrder ℕ-isTotalOrder
ℕ-isPreorder        = IsPartialOrder.isPreorder ℕ-isPartialOrder
≤-refl      = IsPreorder.reflexive ℕ-isPreorder
≤-antisym   = IsPartialOrder.antisym ℕ-isPartialOrder
≤-total     = IsTotalOrder.total ℕ-isTotalOrder



--
-- let remainder = sum `mod` base
--     suc Q     = n `div` base
-- in
--    if sum < n
--        then    sum
--        else    base * Q + remainder

private

    -- some boring lemmas

    >-complement : ∀ {a b} → a N> b → ¬ (a N≤ b)
    >-complement {zero}  ()
    >-complement {suc a} {zero} a>b ()
    >-complement {suc a} {suc b} (s≤s a>b) = contraposition >-complement (λ z → z a>b)

    lem₁ : ∀ m k → suc (m N+ k) N> m
    lem₁ zero k = s≤s z≤n
    lem₁ (suc m) k = s≤s (lem₁ m k)

    lem₂ : ∀ m n → n N≤ m → {≢0 : False (n ≟ 0)} → 0 N< (_div_ m n {≢0})
    lem₂ m       zero    n≤m {()}
    lem₂ zero    (suc n) ()
    lem₂ (suc m) (suc n) n≤m {≢0} with compare m n
    lem₂ (suc m) (suc .(suc (m N+ k))) (s≤s n≤m) {tt} | Nat.less .m k    = contradiction n≤m (>-complement (lem₁ m k))
    lem₂ (suc m) (suc .m)              n≤m            | Nat.equal .m     = s≤s z≤n
    lem₂ (suc .(suc (n N+ k))) (suc n) n≤m            | Nat.greater .n k = s≤s z≤n

    lem₃ : ∀ m n → n N≤ m → {≢0 : False (n ≟ 0)} → m N> Fin⇒ℕ (_mod_ m n {≢0})
    lem₃ m       zero    n≤m {()}
    lem₃ zero    (suc n) ()
    lem₃ (suc m) (suc n) n≤m {≢0} with _divMod_ (suc m) (suc n) {≢0} | inspect (λ x → _divMod_ (suc m) (suc n) {≢0 = x}) ≢0
    lem₃ (suc m) (suc n) n≤m {tt} | result zero remainder property | PropEq.[ eq ] =
        contradiction (≤-refl (cong DivMod.quotient eq)) (>-complement (lem₂ (suc m) (suc n) n≤m))
    lem₃ (suc m) (suc n) n≤m {tt} | result (suc quotient) remainder property | w =
        begin
            suc (Fin⇒ℕ remainder)
        ≤⟨ s≤s (m≤m+n (Fin⇒ℕ remainder) (n N+ quotient N* suc n)) ⟩
            suc (Fin⇒ℕ remainder N+ (n N+ quotient N* suc n))
        ≡⟨ sym (+-suc (Fin⇒ℕ remainder) (n N+ quotient N* suc n)) ⟩
            Fin⇒ℕ remainder N+ suc (n N+ quotient N* suc n)
        ≡⟨ sym property ⟩
            suc m
        ∎
    -- helper function for adding two 'Fin n' with offset 'm'
    -- (m + x) + (m + y) - m = m + x + y
    D+sum : ∀ {n} (m : ℕ) → (x y : Fin n) → ℕ
    D+sum m x y = m N+ (Fin⇒ℕ x) N+ (Fin⇒ℕ y)

_D+_ : ∀ {b m n} → Digit b m n → Digit b m n → Digit b m n
_D+_ {zero}                ()     ()
_D+_ {suc zero}            x      _      = x
_D+_ {suc (suc b)} {m} {n} (Dn x) (Dn y) with suc (D+sum m x y) N≤? n -- see if: sum < n
_D+_ {suc (suc b)} {m} {n} (Dn x) (Dn y {b≤n} {bm≤n}) | yes p =
    Dn (fromℕ≤ {D+sum m x y} p) {b≤n} {bm≤n} -- just return the sum
_D+_ {suc (suc b)} {m} {n} (Dn x) (Dn y {b≤n}) | no ¬p with n divMod (suc (suc b)) | inspect (λ x → _divMod_ n (suc (suc b)) {≢0 = x}) tt -- (D+sum m x y) divMod (suc (suc b))
_D+_ {suc (suc b)} {m} {n} (Dn x) (Dn y {b≤n}) | no ¬p | result zero remainder prop | PropEq.[ eq ] =
    -- prop   : n ≡ remainder + 0
    -- prop'  : n ≤ remainder
    -- lem₃   : n > remainder
    let base = suc (suc b)
        prop' =
            begin
                n
            ≡⟨ trans prop (+-right-identity (Fin⇒ℕ remainder)) ⟩
                Fin⇒ℕ remainder
            ≡⟨ cong (λ w → Fin⇒ℕ (DivMod.remainder w)) (sym eq) ⟩
                Fin⇒ℕ (DivMod.remainder (n divMod suc (suc b)))
            ∎
        ¬lem₃ = >-complement (lem₃ n base b≤n)
    in  contradiction prop' ¬lem₃
_D+_ {suc (suc b)} {m} {n} (Dn x) (Dn y {b≤n} {bm≤n}) | no ¬p | result (suc Q) n%base n-base-prop | PropEq.[ eq ] =
    let base = suc (suc b)
        sum = D+sum m x y
        result _ sum%base _ = _divMod_ sum base {tt}
        sum' = Fin⇒ℕ sum%base N+ Q N* base
        sum'≤n = begin
                suc (Fin⇒ℕ sum%base N+ Q N* base)
            ≡⟨ sym (+-suc (Fin⇒ℕ sum%base) (Q N* base)) ⟩
                Fin⇒ℕ sum%base N+ (1 N+ (Q N* base))
            ≡⟨ sym (+-assoc (Fin⇒ℕ sum%base) 1 (Q N* base)) ⟩
                (Fin⇒ℕ sum%base N+ 1) N+ Q N* base
            ≡⟨ cong (λ w → w N+ Q N* base) (+-comm (Fin⇒ℕ sum%base) 1) ⟩
                suc (Fin⇒ℕ sum%base) N+ Q N* base
            ≤⟨ bounded sum%base +-mono ≤-refl refl ⟩
                base N+ Q N* base
            ≤⟨ m≤m+n (base N+ Q N* base) (Fin⇒ℕ n%base) ⟩
                base N+ Q N* base N+ Fin⇒ℕ n%base
            ≡⟨ +-comm (base N+ Q N* base) (Fin⇒ℕ n%base) ⟩
                Fin⇒ℕ n%base N+ (suc Q) N* base
            ≡⟨ sym n-base-prop ⟩
                n
            ∎
    in Dn (fromℕ≤ {sum'} sum'≤n) {b≤n} {bm≤n}


{-
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
    ∎
-}

--
--  Numeral System:
--
{-}
data System : (basse from range : ℕ) → Set where
    Sys : ∀ {b m n} → List (Digit m n) → System b m n

toℕ : ∀ {b m n} → System b m n → ℕ
toℕ {b} (Sys list) = foldr (shift-then-add b) 0 list
    where   shift-then-add : ∀ {m n} → (base : ℕ) → Digit m n → ℕ → ℕ
            shift-then-add b x acc = (Digit⇒ℕ x) ℕ+ (acc ℕ* b)

_+_ : ∀ {b m n} → System b m n → System b m n → System b m n
Sys []       + Sys ys = Sys ys
Sys xs       + Sys [] = Sys xs
Sys (x ∷ xs) + Sys (y ∷ ys) = {! x  !}

-}
--
--  Example
--

private
    one : Digit 2 1 2
    one = Dn Fz {s≤s (s≤s z≤n)} {s≤s (s≤s z≤n)}

    two : Digit 2 1 2
    two = Dn (Fs Fz) {s≤s (s≤s z≤n)} {s≤s (s≤s z≤n)}

    a0 : Digit 3 0 4
    a0 = Dn Fz {s≤s (s≤s (s≤s z≤n))} {z≤n}

    a1 : Digit 3 0 4
    a1 = Dn (Fs Fz) {s≤s (s≤s (s≤s z≤n))} {z≤n}

    a2 : Digit 3 0 4
    a2 = Dn (Fs (Fs Fz)) {s≤s (s≤s (s≤s z≤n))} {z≤n}

    a3 : Digit 3 0 4
    a3 = Dn (Fs (Fs (Fs Fz))) {s≤s (s≤s (s≤s z≤n))} {z≤n}


    -- a : System 1 1 2
    -- a = Sys (one ∷ two ∷ [])
