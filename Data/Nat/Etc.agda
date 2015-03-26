module Data.Nat.Etc where

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Function
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; trans; sym)
open PropEq.≡-Reasoning

-- exponention
_^_ : ℕ → ℕ → ℕ
a ^ zero  = 1
a ^ suc b = a * (a ^ b)


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

distrib-left-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
distrib-left-*-+ m n o =
        begin
            m * (n + o)
        ≡⟨ *-comm m (n + o) ⟩
            (n + o) * m
        ≡⟨ distribʳ-*-+ m n o ⟩
            n * m + o * m
        ≡⟨ cong (flip _+_ (o * m)) (*-comm n m) ⟩
            m * n + o * m
        ≡⟨ cong (_+_ (m * n)) (*-comm o m) ⟩
            m * n + m * o
        ∎

no-zero-divisor : ∀ m n → m ≢ 0 → m * n ≡ 0 → n ≡ 0
no-zero-divisor zero    n       p q = contradiction q p
no-zero-divisor (suc m) zero    p q = refl
no-zero-divisor (suc m) (suc n) p ()

m^n≢0 : ∀ m n → {m≢0 : m ≢ 0} → m ^ n ≢ 0
m^n≢0 m zero    {p} = λ ()
m^n≢0 m (suc n) {p} = contraposition (no-zero-divisor m (m ^ n) p) (m^n≢0 m n {p})

m≰n⇒n<m : (m n : ℕ) → m ≰ n → m > n
m≰n⇒n<m zero n p = contradiction p (λ z → z z≤n)
m≰n⇒n<m (suc m) zero p = s≤s z≤n
m≰n⇒n<m (suc m) (suc n) p = s≤s (m≰n⇒n<m m n (λ z → p (s≤s z)))

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
