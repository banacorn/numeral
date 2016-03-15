module Data.Fin.Properties.Extra where

open import Data.Nat
    renaming (suc to S; zero to Z; _+_ to _ℕ+_; _*_ to _ℕ*_)
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Extra renaming (suc-injective to S-injective)
open import Data.Nat.Properties.Simple
open import Data.Fin
open import Data.Fin.Properties
open import Data.Product

open import Function
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open DecTotalOrder decTotalOrder renaming (refl to ≤-refl)

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

suc-injective : ∀ {b} {x y : Fin b} → suc x ≡ suc y → x ≡ y
suc-injective {b} {x} {.x} refl = refl

some-lemma : ∀ b x y xs ys
    → toℕ {S b} x ℕ+ xs ℕ* S b ≡ toℕ {S b} y ℕ+ ys ℕ* S b
    → x ≡ y × xs ≡ ys
some-lemma b zero    zero    Z      Z      p = refl , refl
some-lemma b zero    (suc n) Z      Z      ()
some-lemma b (suc m) zero    Z      Z      ()
some-lemma b (suc m) (suc n) Z      Z      p =
    cong suc (toℕ-injective (cancel-+-right Z (S-injective p)))
    , refl
some-lemma b zero    zero    Z      (S ns) ()
some-lemma b zero    (suc n) Z      (S ns) ()
some-lemma b (suc m) zero    Z      (S ns) p = contradiction p ¬p
    where
            ¬p : S (toℕ m ℕ+ Z) ≢ S (b ℕ+ ns ℕ* S b)
            ¬p = <⇒≢ $ s≤s $
                start
                    S (toℕ m ℕ+ Z)
                ≤⟨ reflexive (+-right-identity (S (toℕ m))) ⟩
                    S (toℕ m)
                ≤⟨ bounded m ⟩
                    b
                ≤⟨ m≤m+n b (ns ℕ* S b) ⟩
                    b ℕ+ ns ℕ* S b
                □
some-lemma b (suc m) (suc n) Z      (S ns) p = contradiction p ¬p
    where
            ¬p : S (toℕ m ℕ+ Z) ≢ S (toℕ n ℕ+ S (b ℕ+ ns ℕ* S b))
            ¬p = <⇒≢ $ s≤s $
                start
                    S (toℕ m ℕ+ Z)
                ≤⟨ reflexive (+-right-identity (S (toℕ m))) ⟩
                    S (toℕ m)
                ≤⟨ bounded m ⟩
                    b
                ≤⟨ ≤-step ≤-refl ⟩
                    S b
                ≤⟨ m≤m+n (S b) (ns ℕ* S b) ⟩
                    S (b ℕ+ ns ℕ* S b)
                ≤⟨ n≤m+n (toℕ n) (S (b ℕ+ ns ℕ* S b)) ⟩
                    toℕ n ℕ+ S (b ℕ+ ns ℕ* S b)
                □
some-lemma b zero    zero    (S ms) Z      ()
some-lemma b zero    (suc n) (S ms) Z      p = contradiction p ¬p
    where
            ¬p : S (b ℕ+ ms ℕ* S b) ≢ S (toℕ n ℕ+ Z)
            ¬p = >⇒≢ $ s≤s $
                start
                    S (toℕ n ℕ+ Z)
                ≤⟨ reflexive (+-right-identity (S (toℕ n))) ⟩
                    S (toℕ n)
                ≤⟨ bounded n ⟩
                    b
                ≤⟨ m≤m+n b (ms ℕ* S b) ⟩
                    b ℕ+ ms ℕ* S b
                □
some-lemma b (suc m) zero    (S ms) Z     ()
some-lemma b (suc m) (suc n) (S ms) Z     p = contradiction p ¬p
    where
            ¬p : S (toℕ m ℕ+ S (b ℕ+ ms ℕ* S b)) ≢ S (toℕ n ℕ+ Z)
            ¬p = >⇒≢ $ s≤s $
                start
                    S (toℕ n ℕ+ Z)
                ≤⟨ reflexive (+-right-identity (S (toℕ n))) ⟩
                    S (toℕ n)
                ≤⟨ bounded n ⟩
                    b
                ≤⟨ ≤-step ≤-refl ⟩
                    S b
                ≤⟨ m≤m+n (S b) (ms ℕ* S b) ⟩
                    S (b ℕ+ ms ℕ* S b)
                ≤⟨ n≤m+n (toℕ m) (S (b ℕ+ ms ℕ* S b)) ⟩
                    toℕ m ℕ+ S (b ℕ+ ms ℕ* S b)
                □
some-lemma b zero    zero    (S ms) (S ns) p =
    refl
    , (cong S (cancel-*-right ms ns {b} (cancel-+-left b (S-injective p))))
some-lemma b zero    (suc n) (S ms) (S ns) p = (proj₁ ind) , cong S (proj₂ ind)
    where
            p' : S b ℕ+ ms ℕ* S b ≡ S b ℕ+ S (toℕ n ℕ+ ns ℕ* S b)
            p' = begin
                    S (b ℕ+ ms ℕ* S b)
                ≡⟨ p ⟩
                    S (toℕ n ℕ+ S (b ℕ+ ns ℕ* S b))
                ≡⟨ sym (+-assoc (S (toℕ n)) (S b) (ns ℕ* S b)) ⟩
                    (S (toℕ n) ℕ+ S b) ℕ+ ns ℕ* S b
                ≡⟨ cong (λ x → x ℕ+ ns ℕ* S b) (+-comm (S (toℕ n)) (S b)) ⟩
                    S (b ℕ+ S (toℕ n) ℕ+ ns ℕ* S b)
                ≡⟨ +-assoc (S b) (S (toℕ n)) (ns ℕ* S b) ⟩
                    S (b ℕ+ S (toℕ n ℕ+ ns ℕ* S b))
                ∎
            ind : zero ≡ suc n × ms ≡ ns
            ind = some-lemma b zero (suc n) ms ns (cancel-+-left (S b) p')
some-lemma b (suc m) zero    (S ms) (S ns) p = (proj₁ ind) , (cong S (proj₂ ind))
    where
            p' : S b ℕ+ (S (toℕ m) ℕ+ ms ℕ* S b) ≡ S b ℕ+ ns ℕ* S b
            p' = begin
                    S b ℕ+ S (toℕ m ℕ+ ms ℕ* S b)
                ≡⟨ sym (+-assoc (S b) (S (toℕ m)) (ms ℕ* S b)) ⟩
                    S (b ℕ+ S (toℕ m) ℕ+ ms ℕ* S b)
                ≡⟨ cong (λ x → x ℕ+ ms ℕ* S b) (+-comm (S b) (S (toℕ m))) ⟩
                    S (toℕ m ℕ+ S b ℕ+ ms ℕ* S b)
                ≡⟨ +-assoc (S (toℕ m)) (S b) (ms ℕ* S b) ⟩
                    S (toℕ m ℕ+ S (b ℕ+ ms ℕ* S b))
                ≡⟨ p ⟩
                    S (b ℕ+ ns ℕ* S b)
                ∎
            ind : suc m ≡ zero × ms ≡ ns
            ind = some-lemma b (suc m) zero ms ns (cancel-+-left (S b) p')
some-lemma b (suc m) (suc n) (S ms) (S ns) p = (proj₁ ind) , (cong S (proj₂ ind))
    where
            p' : S (b ℕ+ S (toℕ m ℕ+ ms ℕ* S b)) ≡ S (b ℕ+ S (toℕ n ℕ+ ns ℕ* S b))
            p' = begin
                    S (b ℕ+ S (toℕ m ℕ+ ms ℕ* S b))
                ≡⟨ sym (+-assoc (S b) (S (toℕ m)) (ms ℕ* S b)) ⟩
                    S (b ℕ+ S (toℕ m) ℕ+ ms ℕ* S b)
                ≡⟨ cong (λ x → x ℕ+ ms ℕ* S b) (+-comm (S b) (S (toℕ m))) ⟩
                    S (toℕ m ℕ+ S b ℕ+ ms ℕ* S b)
                ≡⟨ +-assoc (S (toℕ m)) (S b) (ms ℕ* S b) ⟩
                    S (toℕ m ℕ+ S (b ℕ+ ms ℕ* S b))
                ≡⟨ p ⟩
                    S (toℕ n ℕ+ S (b ℕ+ ns ℕ* S b))
                ≡⟨ sym (+-assoc (S (toℕ n)) (S b) (ns ℕ* S b)) ⟩
                    S (toℕ n ℕ+ S b ℕ+ ns ℕ* S b)
                ≡⟨ cong (λ x → x ℕ+ ns ℕ* S b) (+-comm (S (toℕ n)) (S b)) ⟩
                    S (b ℕ+ S (toℕ n) ℕ+ ns ℕ* S b)
                ≡⟨ +-assoc (S b) (S (toℕ n)) (ns ℕ* S b) ⟩
                    S (b ℕ+ S (toℕ n ℕ+ ns ℕ* S b))
                ∎
            ind : suc m ≡ suc n × ms ≡ ns
            ind = some-lemma b (suc m) (suc n) ms ns (cancel-+-left (S b) p')
