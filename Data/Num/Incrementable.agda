module Data.Num.Incrementable where

open import Data.Num.Core
open import Data.Num.Bounded
open import Data.Num.Maximum
open import Data.Num.Next

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra

open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤)
    renaming (zero to z; suc to s)

open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)
open import Data.Product
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import Function
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)

------------------------------------------------------------------------
-- a number is incrementable if there exists some n' : Num b d o such that ⟦ n' ⟧ℕ ≡ suc ⟦ n ⟧ℕ

Incrementable : ∀ {b d o} → (xs : Num b d o) → Set
Incrementable {b} {d} {o} xs = Σ[ xs' ∈ Num b d o ] ⟦ xs' ⟧ ≡ suc ⟦ xs ⟧

m≡1+n⇒m>n : ∀ {m n} → m ≡ suc n → m > n
m≡1+n⇒m>n {zero}  {n}  ()
m≡1+n⇒m>n {suc m} {.m} refl = s≤s ≤-refl

Maximum⇒¬Incrementable : ∀ {b d o}
    → (xs : Num b d o)
    → (max : Maximum xs)
    → ¬ (Incrementable xs)
Maximum⇒¬Incrementable xs max (evidence , claim)
    = contradiction (max evidence) (>⇒≰ (m≡1+n⇒m>n claim))
--
-- -- begin
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≡⟨ {!   !} ⟩
-- --     {!   !}
-- -- ∎
--
-- -- start
-- --     {!   !}
-- -- ≤⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≤⟨ {!   !} ⟩
-- --     {!   !}
-- -- ≤⟨ {!   !} ⟩
-- --     {!   !}
-- -- □
--
--
--
--
-- mutual
--
--
--
--
--     Incrementable-NullBase :  ∀ {d o}
--         → (xs : Num 0 (suc d) o)
--         → (¬max : ¬ (Maximum xs))
--         → Incrementable xs
--     Incrementable-NullBase {d} {o} xs ¬max = (next-number-NullBase xs ¬max) , {!   !}
--     -- Incrementable-NullBase :  ∀ {d o}
--     --     → (xs : Num 0 (suc d) o)
--     --     → (¬max : ¬ (Maximum xs))
--     --     → Incrementable xs
--     -- Incrementable-NullBase {d} {o} xs ¬max with NullBase-view d o
--     -- Incrementable-NullBase xs       ¬max | AllZeros = contradiction (AllZeros-Maximum xs) ¬max
--     -- Incrementable-NullBase xs       ¬max | Others bound with Greatest? (lsd xs)
--     -- Incrementable-NullBase xs       ¬max | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ¬max
--     -- Incrementable-NullBase (x ∙)    ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∙ , Digit-toℕ-digit+1 x ¬greatest
--     -- Incrementable-NullBase (x ∷ xs) ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∷ xs , cong (λ w → w + ⟦ xs ⟧ * 0) (Digit-toℕ-digit+1 x ¬greatest)
--
--     Incrementable-Others-Abundant :  ∀ {b d o}
--         → (xs : Num (suc b) (suc d) o)
--         → (¬max : ¬ (Maximum xs))
--         → (d+o≥2 : 2 ≤ suc (d + o))
--         → (abundant : Abundant (suc b) (suc d) o)
--         → Incrementable xs
--     Incrementable-Others-Abundant {b} {d} {o} xs ¬max d+o≥2 abundant with cmp (⟦ next-number-Others xs ¬max d+o≥2 ⟧ ∸ ⟦ xs ⟧) 1
--     Incrementable-Others-Abundant {b} {d} {o} xs ¬max d+o≥2 abundant | tri< p ¬q ¬r
--         = contradiction p ¬p
--         where
--             next : Num (suc b) (suc d) o
--             next = next-number-Others xs ¬max d+o≥2
--
--             next>xs : ⟦ next ⟧ > ⟦ xs ⟧
--             next>xs = next-number-is-greater-Others xs ¬max d+o≥2
--
--             ¬p : suc (⟦ next ⟧ ∸ ⟦ xs ⟧) ≰ 1
--             ¬p = >⇒≰ $ s≤s $ +n-mono-inverse ⟦ xs ⟧ $
--                 start
--                     1 + ⟦ xs ⟧
--                 ≤⟨ next>xs ⟩
--                     ⟦ next ⟧
--                 ≈⟨ sym (m∸n+n≡m (<⇒≤ next>xs)) ⟩
--                     ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
--                 □
--     Incrementable-Others-Abundant {b} {d} {o} xs ¬max d+o≥2 abundant | tri≈ ¬p q ¬r
--         = next , proof
--         where
--             next : Num (suc b) (suc d) o
--             next = next-number-Others xs ¬max d+o≥2
--
--             next>xs : ⟦ next ⟧ > ⟦ xs ⟧
--             next>xs = next-number-is-greater-Others xs ¬max d+o≥2
--
--             proof : ⟦ next ⟧ ≡ suc ⟦ xs ⟧
--             proof = begin
--                     ⟦ next ⟧
--                 ≡⟨ sym (m∸n+n≡m (<⇒≤ next>xs)) ⟩
--                     ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
--                 ≡⟨ cong (λ w → w + ⟦ xs ⟧) q ⟩
--                     suc ⟦ xs ⟧
--                 ∎
--     Incrementable-Others-Abundant {b} {d} {o} (x ∙) ¬max d+o≥2 abundant | tri> ¬p ¬q r with Others-view-single b d o x
--     Incrementable-Others-Abundant {b} {d} {o} (x ∙) ¬max d+o≥2 abundant | tri> ¬p ¬q r | NeedNoCarry ¬greatest
--         = next , proof
--         where
--             next : Num (suc b) (suc d) o
--             next = digit+1 x ¬greatest ∙
--
--             proof : ⟦ next ⟧ ≡ suc ⟦ _∙ {suc b} x ⟧
--             proof = Digit-toℕ-digit+1 x ¬greatest
--     Incrementable-Others-Abundant {b} {d} {o} (x ∙) ¬max d+o≥2 abundant | tri> ¬p ¬q r | Gapped greatest gapped
--         = next , proof
--         where
--             eq : (1 ⊔ o) * suc b ≡ suc d
--             eq = IsPartialOrder.antisym isPartialOrder abundant gapped
--
--             next : Num (suc b) (suc d) o
--             next = z ∷ 1⊔o d o d+o≥2 ∙
--
--             proof : ⟦ next ⟧ ≡ suc ⟦ _∙ {suc b} x ⟧
--             proof = begin
--                     o + Digit-toℕ (1⊔o d o d+o≥2) o * suc b
--                 ≡⟨ cong (λ w → o + w * suc b) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
--                     o + (suc zero ⊔ o) * suc b
--                 ≡⟨ cong (λ w → o + w) eq ⟩
--                     o + suc d
--                 ≡⟨ cong (λ w → o + w) (sym greatest) ⟩
--                     o + suc (Fin.toℕ x)
--                 ≡⟨ +-comm o (suc (Fin.toℕ x)) ⟩
--                     suc (Fin.toℕ x + o)
--                 ∎
--
--     Incrementable-Others-Abundant {b} {d} {o} (x ∙) ¬max d+o≥2 abundant | tri> ¬p ¬q r | ¬Gapped greatest ¬gapped
--         = next , proof
--         where
--             lower-bound : (1 ⊔ o) * suc b > 0
--             lower-bound = m≤m⊔n 1 o *-mono s≤s z≤n
--
--             upper-bound : (suc zero ⊔ o) * suc b ≤ suc (Fin.toℕ x + o)
--             upper-bound = start
--                     (suc zero ⊔ o) * suc b
--                 ≤⟨ ≤-pred ¬gapped ⟩
--                     d
--                 ≈⟨ suc-injective (sym greatest) ⟩
--                     Fin.toℕ x
--                 ≤⟨ ≤-step (m≤m+n (Fin.toℕ x) o) ⟩
--                     suc (Fin.toℕ x + o)
--                 □
--             next : Num (suc b) (suc d) o
--             next = digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound ∷ 1⊔o d o d+o≥2 ∙
--
--             proof : ⟦ next ⟧ ≡ suc ⟦ _∙ {suc b} x ⟧
--             proof = begin
--                     Digit-toℕ (digit+1-n x greatest ((1 ⊔ o) * suc b) lower-bound) o + Digit-toℕ (1⊔o d o d+o≥2) o * suc b
--                 ≡⟨ cong₂ (λ v w → v + w * suc b) (Digit-toℕ-digit+1-n x greatest ((suc zero ⊔ o) * suc b) lower-bound abundant) (Digit-toℕ-1⊔o d o d+o≥2) ⟩
--                     ((suc (Fin.toℕ x + o) ∸ (suc zero ⊔ o) * suc b) + (suc zero ⊔ o) * suc b)
--                 ≡⟨ m∸n+n≡m {suc (Fin.toℕ x + o)} {(suc zero ⊔ o) * suc b} upper-bound ⟩
--                     suc (Fin.toℕ x + o)
--                 ∎
--     Incrementable-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max d+o≥2 abundant | tri> ¬p ¬q r with Others-view x xs ¬max d+o≥2
--     Incrementable-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max d+o≥2 abundant | tri> ¬p ¬q r | NeedNoCarry ¬greatest
--         = next , proof
--         where
--             next : Num (suc b) (suc d) o
--             next = digit+1 x ¬greatest ∷ xs
--
--             proof : ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
--             proof = cong (λ w → w + ⟦ xs ⟧ * suc b) (Digit-toℕ-digit+1 x ¬greatest)
--
--     Incrementable-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max d+o≥2 abundant | tri> ¬p ¬q r | Gapped greatest gapped
--         = next , proof
--         where
--
--             ¬max-xs : ¬ (Maximum xs)
--             ¬max-xs = next-number-¬Maximum xs d+o≥2
--
--             next-xs : Num (suc b) (suc d) o
--             next-xs = next-number-Others xs ¬max-xs d+o≥2
--
--             temp = Incrementable-Others-Abundant xs ¬max-xs d+o≥2 abundant
--
--             -- ⟦next-xs⟧∸⟦xs⟧≡1 : ⟦ next-xs ⟧ ∸ ⟦ xs ⟧ ≡ 1
--             -- ⟦next⟧∸⟦xs⟧≡1 = cancel-+-right ⟦ xs ⟧ {⟦ next ⟧ ∸ ⟦ xs ⟧} {1} $
--             --     begin
--             --         ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
--             --     ≡⟨ m∸n+n≡m next>xs ⟩
--             --         ⟦ next ⟧
--             --     ≡⟨ ? ⟩
--             --         1 + ⟦ xs ⟧
--             --     ∎
--
--             next : Num (suc b) (suc d) o
--             next = z ∷ next-xs
--
--             proof : ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
--             proof =
--                 begin
--                     o + ⟦ next-xs ⟧ * suc b
--                 ≡⟨ cong (λ w → (o + w * suc b)) {! proj₂ temp  !} ⟩
--                     o + (suc b + ⟦ xs ⟧ * suc b)
--                 ≡⟨ sym (+-assoc o (suc b) (⟦ xs ⟧ * suc b)) ⟩
--                     o + suc b + ⟦ xs ⟧ * suc b
--                 ≡⟨ cong (λ w → o + w + ⟦ xs ⟧ * suc b) {!   !} ⟩
--                     o + suc d + ⟦ xs ⟧ * suc b
--                 ≡⟨ cong (λ w → o + w + ⟦ xs ⟧ * suc b) (sym greatest) ⟩
--                     o + suc (Fin.toℕ x) + ⟦ xs ⟧ * suc b
--                 ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) (+-comm o (suc (Fin.toℕ x))) ⟩
--                     suc (Fin.toℕ x + o + ⟦ xs ⟧ * suc b)
--                 ∎
--
--                 -- begin
--                 --     o + ⟦ next-xs ⟧ * suc b
--                 -- ≡⟨ cong (λ w → (o + w * suc b)) ? ⟩
--                 --     o + (suc b + ⟦ next-xs ⟧ * suc b)
--                 -- ≡⟨ sym (+-assoc o (suc b) (⟦ next-xs ⟧ * suc b)) ⟩
--                 --     o + suc b + ⟦ next-xs ⟧ * suc b
--                 -- ≡⟨ cong (λ w → o + w + ⟦ next-xs ⟧ * suc b) ? ⟩
--                 --     o + suc d + ⟦ next-xs ⟧ * suc b
--                 -- ≡⟨ cong (λ w → o + w + ⟦ next-xs ⟧ * suc b) (sym greatest) ⟩
--                 --     o + suc (Fin.toℕ x) + ⟦ next-xs ⟧ * suc b
--                 -- ≡⟨ cong (λ w → w + ⟦ next-xs ⟧ * suc b) (+-comm o (suc (Fin.toℕ x))) ⟩
--                 --     suc (Fin.toℕ x + o + ⟦ next-xs ⟧ * suc b)
--                 -- ∎
--
--     Incrementable-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max d+o≥2 abundant | tri> ¬p ¬q r | ¬Gapped greatest ¬gapped = {!   !}
--
-- -- Incrementable-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max d+o≥2 abundant | Gapped greatest gapped
-- --     = {!   !} , {!   !}
-- --     where
-- --         xs-¬max : ¬ (Maximum xs)
-- --         xs-¬max = next-number-¬Maximum xs d+o≥2
-- --
-- --         xs-incrementable : Incrementable xs
-- --         xs-incrementable = Incrementable-Others-Abundant xs xs-¬max d+o≥2 abundant
-- --
-- --         xs-next : Num (suc b) (suc d) o
-- --         xs-next = proj₁ xs-incrementable
--
--         --
--         -- next>xs : ⟦ xs-next ⟧ > ⟦ xs ⟧
--         -- next>xs = next-number-is-greater-Others xs ? d+o≥2
--         --
--         -- ⟦next⟧∸⟦xs⟧≡1 : ⟦ next ⟧ ∸ ⟦ xs ⟧ ≡ 1
--         -- ⟦next⟧∸⟦xs⟧≡1 = cancel-+-right ⟦ xs ⟧ {⟦ next ⟧ ∸ ⟦ xs ⟧} {1} $
--         --     begin
--         --         ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
--         --     ≡⟨ m∸n+n≡m (<⇒≤ next>xs) ⟩
--         --         ⟦ next ⟧
--         --     ≡⟨ {!   !} ⟩
--         --         1 + ⟦ xs ⟧
--         --     ∎
--
--         -- ¬redundant : suc b ≥ suc d
--         -- ¬redundant =
--         --     start
--         --         suc d
--         --     ≤⟨ gapped ⟩
--         --         (⟦ next ⟧ ∸ ⟦ xs ⟧) * suc b
--         --     ≈⟨ cong (λ w → w * suc b) ⟦next⟧∸⟦xs⟧≡1 ⟩
--         --         suc (b + zero)
--         --     ≈⟨ +-right-identity (suc b) ⟩
--         --         suc b
--         --     □
--         -- abundant' : suc b ≤ suc d
--         -- abundant' =
--         --     start
--         --         suc b
--         --     ≈⟨ sym (+-right-identity (suc b)) ⟩
--         --         suc (b + zero)
--         --     ≤⟨ *n-mono (suc b) (m≤m⊔n 1 o) ⟩
--         --         (suc zero ⊔ o) * suc b
--         --     ≤⟨ abundant ⟩
--         --         suc d
--         --     □
--         -- b≡d : suc b ≡ suc d
--         -- b≡d = IsPartialOrder.antisym isPartialOrder abundant' ¬redundant
--         --
--         --
--         -- proof : ⟦ next ⟧ ≡ suc ⟦ x ∷ xs ⟧
--         -- proof = begin
--         --         o + ⟦ next ⟧ * suc b
--         --     ≡⟨ cong (λ w → (o + w * suc b)) ? ⟩
--         --         o + (suc b + ⟦ xs ⟧ * suc b)
--         --     ≡⟨ sym (+-assoc o (suc b) (⟦ xs ⟧ * suc b)) ⟩
--         --         o + suc b + ⟦ xs ⟧ * suc b
--         --     ≡⟨ cong (λ w → o + w + ⟦ xs ⟧ * suc b) b≡d ⟩
--         --         o + suc d + ⟦ xs ⟧ * suc b
--         --     ≡⟨ cong (λ w → o + w + ⟦ xs ⟧ * suc b) (sym greatest) ⟩
--         --         o + suc (Fin.toℕ x) + ⟦ xs ⟧ * suc b
--         --     ≡⟨ cong (λ w → w + ⟦ xs ⟧ * suc b) (+-comm o (suc (Fin.toℕ x))) ⟩
--         --         suc (Fin.toℕ x + o + ⟦ xs ⟧ * suc b)
--         --     ∎
-- -- Incrementable-Others-Abundant {b} {d} {o} (x ∷ xs) ¬max d+o≥2 abundant | ¬Gapped greatest ¬gapped = {!   !}
--
--
--
-- --
-- -- Incrementable-Others :  ∀ {b d o}
-- --     → (xs : Num b d o)
-- --     → (¬max : ¬ (Maximum xs))
-- --     → Dec (Incrementable xs)
-- -- Incrementable-Others xs ¬max with cmp (⟦ next-number xs ¬max ⟧ ∸ ⟦ xs ⟧) 1
-- -- Incrementable-Others xs ¬max | tri< p ¬q ¬r = contradiction p (>⇒≰ (s≤s ¬p))
-- --     where
-- --          next  = next-number xs ¬max
-- --          ¬p : ⟦ next ⟧ ∸ ⟦ xs ⟧ > 0
-- --          ¬p = +n-mono-inverse ⟦ xs ⟧ $
-- --             start
-- --                 1 + ⟦ xs ⟧
-- --             ≤⟨ next-number-is-greater xs ¬max ⟩
-- --                 (⟦ next ⟧)
-- --             ≈⟨ sym (m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs ¬max))) ⟩
-- --                 ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
-- --             □
-- -- Incrementable-Others xs ¬max | tri≈ ¬p q ¬r = yes (next-number xs ¬max , prop)
-- --     where
-- --         next  = next-number xs ¬max
-- --         prop : ⟦ next ⟧ ≡ suc ⟦ xs ⟧
-- --         prop =
-- --             begin
-- --                 (⟦ next ⟧)
-- --             ≡⟨ sym (m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs ¬max))) ⟩
-- --                 ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
-- --             ≡⟨ cong (λ w → w + ⟦ xs ⟧) q ⟩
-- --                 suc ⟦ xs ⟧
-- --             ∎
-- -- Incrementable-Others xs ¬max | tri> ¬p ¬q r = no prop
-- --     where
-- --         next  = next-number xs ¬max
-- --         prop : ¬ Incrementable xs
-- --         prop (evidence , claim) = contradiction ⟦next⟧>⟦evidence⟧ ⟦next⟧≯⟦evidence⟧
-- --             where
-- --                 ⟦next⟧>⟦evidence⟧ : ⟦ next ⟧ > ⟦ evidence ⟧
-- --                 ⟦next⟧>⟦evidence⟧ =
-- --                     start
-- --                         suc ⟦ evidence ⟧
-- --                     ≈⟨ cong suc claim ⟩
-- --                         2 + ⟦ xs ⟧
-- --                     ≤⟨ +n-mono ⟦ xs ⟧ r ⟩
-- --                         ⟦ next ⟧ ∸ ⟦ xs ⟧ + ⟦ xs ⟧
-- --                     ≈⟨ m∸n+n≡m (≤-pred $ ≤-step $ (next-number-is-greater xs ¬max)) ⟩
-- --                         ⟦ next ⟧
-- --                     □
-- --                 ⟦next⟧≯⟦evidence⟧ : ⟦ next ⟧ ≯ ⟦ evidence ⟧
-- --                 ⟦next⟧≯⟦evidence⟧ = ≤⇒≯ (next-number-is-LUB xs evidence ¬max (m≡1+n⇒m>n claim))
--
--     Incrementable? : ∀ {b d o}
--         → (xs : Num b d o)
--         → Dec (Incrementable xs)
--     Incrementable? {b} {d} {o} xs with Maximum? xs
--     Incrementable? {b} {d} {o} xs | yes max = no (Maximum⇒¬Incrementable xs max)
--     Incrementable? {b} {d} {o} xs | no ¬max with boundedView b d o
--     Incrementable? xs | no ¬max | IsBounded (NullBase d o) = yes (Incrementable-NullBase xs ¬max)
--     Incrementable? xs | no ¬max | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
--     Incrementable? xs | no ¬max | IsntBounded (Others b d o d+o≥2) with Abundant? (suc b) (suc d) o
--     Incrementable? xs | no ¬max | IsntBounded (Others b d o d+o≥2) | yes abundant = yes (Incrementable-Others-Abundant xs ¬max d+o≥2 abundant)
--     Incrementable? xs | no ¬max | IsntBounded (Others b d o d+o≥2) | no ¬abundant = {!    !}
--     Incrementable? xs | no ¬max | IsntBounded (NoDigits b o) = NoDigits-explode xs
--
--     increment : ∀ {b d o}
--         → (xs : Num b d o)
--         → Incrementable xs
--         → Num b d o
--     increment xs (next , claim) = next
--
--     increment-next-number-NullBase : ∀ {d o}
--         → (xs : Num 0 (suc d) o)
--         → (¬max : ¬ (Maximum xs))
--         → (incr : Incrementable xs)
--         → increment xs incr ≡ next-number-NullBase xs ¬max
--     increment-next-number-NullBase {d} {o} xs ¬max incr with NullBase-view d o
--     increment-next-number-NullBase xs ¬max incr | AllZeros = AllZeros-explode xs ¬max
--     increment-next-number-NullBase xs ¬max incr | Others bound with Greatest? (lsd xs)
--     increment-next-number-NullBase xs ¬max incr | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ¬max
--     increment-next-number-NullBase (x ∙) ¬max (proj₁ , proj₂) | Others bound | no ¬greatest = {!   !}
--         -- begin
--         --     proj₁ incr
--         -- ≡⟨ refl ⟩
--         --     {!   !}
--         -- ≡⟨ {!   !} ⟩
--         --     {!   !}
--         -- ≡⟨ {!   !} ⟩
--         --     {!   !}
--         -- ≡⟨ {!   !} ⟩
--         --     digit+1 x ¬greatest ∙
--         -- ∎
--     increment-next-number-NullBase (x ∷ xs) ¬max incr | Others bound | no ¬greatest = {!   !}
--
--     -- Incrementable-NullBase {d} {o} xs ¬max with NullBase-view d o
--     -- Incrementable-NullBase xs       ¬max | AllZeros = contradiction (AllZeros-Maximum xs) ¬max
--     -- Incrementable-NullBase xs       ¬max | Others bound with Greatest? (lsd xs)
--     -- Incrementable-NullBase xs       ¬max | Others bound | yes greatest = contradiction (NullBase-Maximum xs greatest) ¬max
--     -- Incrementable-NullBase (x ∙)    ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∙ , Digit-toℕ-digit+1 x ¬greatest
--     -- Incrementable-NullBase (x ∷ xs) ¬max | Others bound | no ¬greatest = digit+1 x ¬greatest ∷ xs , cong (λ w → w + ⟦ xs ⟧ * 0) (Digit-toℕ-digit+1 x ¬greatest)
--
--
--     increment-next-number : ∀ {b d o}
--         → (xs : Num b d o)
--         → (¬max : ¬ (Maximum xs))
--         → (incr : Incrementable xs)
--         → increment xs incr ≡ next-number xs ¬max
--     increment-next-number {b} {d} {o} xs ¬max incr with boundedView b d o
--     increment-next-number xs ¬max incr | IsBounded (NullBase d o) = increment-next-number-NullBase xs ¬max incr
--     increment-next-number xs ¬max incr | IsBounded (AllZeros b) = AllZeros-explode xs ¬max
--     increment-next-number xs ¬max incr | IsntBounded (Others b d o d+o≥2) = {!   !}
--     increment-next-number xs ¬max incr | IsntBounded (NoDigits b o) = NoDigits-explode xs

-- Continuous (suc b) (suc d) (suc zero)
-- d≥[1⊔o]*b⇒Continuous : ∀ {b d o} → d ≥ (1 ⊔ o) * b → Continuous b d o
-- d≥[1⊔o]*b⇒Continuous {b} {d} {zero} cond = 0 , StartsFrom0-Continuous (≤-trans (reflexive (sym (+-right-identity b))) cond)
-- d≥[1⊔o]*b⇒Continuous {b} {d} {suc zero} cond = {!   !}
-- d≥[1⊔o]*b⇒Continuous {b} {d} {suc (suc o)} cond = {!o   !}


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

-- start
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- ≤⟨ {!   !} ⟩
--     {!   !}
-- □
