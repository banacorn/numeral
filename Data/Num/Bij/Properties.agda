module Data.Num.Bij.Properties where

open import Data.Num.Bij renaming (_+B_ to _+_; _*B_ to _*_)

open import Data.List
open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; cong; sym; trans)
open PropEq.≡-Reasoning

--------------------------------------------------------------------------------


1∷≡incrB∘*2 : ∀ m → one ∷ m ≡ incrB (*2 m)
1∷≡incrB∘*2 []         = refl
1∷≡incrB∘*2 (one ∷ ms) = cong (λ x → one ∷ x)       (1∷≡incrB∘*2 ms)
1∷≡incrB∘*2 (two ∷ ms) = cong (λ x → one ∷ incrB x) (1∷≡incrB∘*2 ms)

split-∷ : ∀ m ms → m ∷ ms ≡ (m ∷ []) + *2 ms
split-∷ m [] = refl
split-∷ one (one ∷ ns) = cong (λ x → one ∷ x)       (1∷≡incrB∘*2 ns)
split-∷ one (two ∷ ns) = cong (λ x → one ∷ incrB x) (1∷≡incrB∘*2 ns)
split-∷ two (one ∷ ns) = cong (λ x → two ∷ x)       (1∷≡incrB∘*2 ns)
split-∷ two (two ∷ ns) = cong (λ x → two ∷ incrB x) (1∷≡incrB∘*2 ns)

+B-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
+B-assoc []       _ _ = refl
+B-assoc (m ∷ ms) n o =
    begin
        (m ∷ ms) + n + o
    ≡⟨ cong (λ x → x + n + o) (split-∷ m ms) ⟩
        (m ∷ []) + *2 ms + n + o
    ≡⟨ cong (λ x → x + o) (+B-assoc (m ∷ []) (*2 ms) n) ⟩
        (m ∷ []) + (*2 ms + n) + o
    ≡⟨ +B-assoc (m ∷ []) (*2 ms + n) o ⟩
        (m ∷ []) + ((*2 ms + n) + o)
    ≡⟨ cong (λ x → (m ∷ []) + x) (+B-assoc (*2 ms) n o) ⟩
        (m ∷ []) + (*2 ms + (n + o))
    ≡⟨ sym (+B-assoc (m ∷ []) (*2 ms) (n + o))  ⟩
        (m ∷ []) + *2 ms + (n + o)
    ≡⟨ cong (λ x → x + (n + o)) (sym (split-∷ m ms)) ⟩
        (m ∷ ms) + (n + o)
    ∎

+B-right-identity : ∀ n → n + [] ≡ n
+B-right-identity []       = refl
+B-right-identity (n ∷ ns) = refl

+B-comm : ∀ m n → m + n ≡ n + m
+B-comm []       n = sym (+B-right-identity n)
+B-comm (m ∷ ms) n =
    begin
        (m ∷ ms) + n
    ≡⟨ cong (λ x → x + n) (split-∷ m ms) ⟩
        (m ∷ []) + *2 ms + n
    ≡⟨ +B-comm ((m ∷ []) + *2 ms) n ⟩
        n + ((m ∷ []) + *2 ms)
    ≡⟨ cong (λ x → n + x) (sym (split-∷ m ms)) ⟩
        n + (m ∷ ms)
    ∎
{-
    begin
        (m ∷ ms) + n
    ≡⟨ cong (λ x → x + n) (split-∷ m ms) ⟩
        (m ∷ []) + *2 ms + n
    ≡⟨ +B-assoc (m ∷ []) (*2 ms) n ⟩
        (m ∷ []) + (*2 ms + n)
    ≡⟨ cong (λ x → (m ∷ []) + x) (+B-comm (*2 ms) n) ⟩
        (m ∷ []) + (n + *2 ms)
    ≡⟨ sym (+B-assoc (m ∷ []) n (*2 ms)) ⟩
        (m ∷ []) + n + *2 ms
    ≡⟨ cong (λ x → x + *2 ms) (+B-comm (m ∷ []) n) ⟩
        n + (m ∷ []) + *2 ms
    ≡⟨ +B-assoc n (m ∷ []) (*2 ms) ⟩
        n + ((m ∷ []) + *2 ms)
    ≡⟨ cong (λ x → n + x) (sym (split-∷ m ms)) ⟩
        n + (m ∷ ms)
    ∎
-}
+B-*2-distrib : ∀ m n → *2 (m + n) ≡ *2 m + *2 n
+B-*2-distrib []       n = refl
+B-*2-distrib (m ∷ ms) n =
    begin
        *2 ((m ∷ ms) + n)
    ≡⟨ cong (λ x → *2 (x + n)) (split-∷ m ms) ⟩
        *2 ((m ∷ []) + *2 ms + n)
    ≡⟨ +B-*2-distrib ((m ∷ []) + *2 ms) n ⟩
        *2 ((m ∷ []) + *2 ms) + *2 n
    ≡⟨ cong (λ x → *2 x + *2 n) (sym (split-∷ m ms)) ⟩
        *2 (m ∷ ms) + *2 n
    ∎


+B-*B-incrB : ∀ m n → m * incrB n ≡ m + m * n
+B-*B-incrB []         n = refl
+B-*B-incrB (m ∷ ms) n =
    begin
        (m ∷ ms) * incrB n
    ≡⟨ cong (λ x → x * incrB n) (split-∷ m ms) ⟩
        ((m ∷ []) + *2 ms) * incrB n
    ≡⟨ +B-*B-incrB ((m ∷ []) + *2 ms) n ⟩
        (m ∷ []) + *2 ms + ((m ∷ []) + *2 ms) * n
    ≡⟨ cong (λ x → x + x * n) (sym (split-∷ m ms)) ⟩
        (m ∷ ms) + (m ∷ ms) * n
    ∎

*B-right-[] : ∀ n → n * [] ≡ []
*B-right-[] [] = refl
*B-right-[] (one ∷ ns) = cong *2_ (*B-right-[] ns)
*B-right-[] (two ∷ ns) = cong *2_ (*B-right-[] ns)

*B-+B-distrib : ∀ m n o → (n + o) * m ≡ n * m + o * m
*B-+B-distrib m []       o = refl
*B-+B-distrib m (n ∷ ns) o =
    begin
        ((n ∷ ns) + o) * m
    ≡⟨ cong (λ x → (x + o) * m) (split-∷ n ns) ⟩
        ((n ∷ []) + *2 ns + o) * m
    ≡⟨ *B-+B-distrib m ((n ∷ []) + *2 ns) o ⟩
        ((n ∷ []) + *2 ns) * m + o * m
    ≡⟨ cong (λ x → x * m + o * m) (sym (split-∷ n ns)) ⟩
        (n ∷ ns) * m + o * m
    ∎

*B-comm : ∀ m n → m * n ≡ n * m
*B-comm []         n = sym (*B-right-[] n)
*B-comm (m ∷ ms) n =
    begin
        (m ∷ ms) * n
    ≡⟨ cong (λ x → x * n) (split-∷ m ms) ⟩
        ((m ∷ []) + *2 ms) * n
    ≡⟨ *B-comm ((m ∷ []) + *2 ms) n ⟩
        n * ((m ∷ []) + *2 ms)
    ≡⟨ cong (λ x → n * x) (sym (split-∷ m ms)) ⟩
        n * (m ∷ ms)
    ∎

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
{-
+B-*B-incrB : ∀ m n → m * incrB n ≡ m + m * n
+B-*B-incrB []         n = refl
+B-*B-incrB (one ∷ ms) [] = {!   !}
+B-*B-incrB (one ∷ ms) (n ∷ ns) = {!   !}
    begin
        incrB n + ms * incrB n
    ≡⟨ cong (λ x → incrB n + x) (+B-*B-incrB ms n) ⟩
        incrB n + (ms + ms * n)
    ≡⟨ sym (+B-assoc (incrB n) ms (ms * n)) ⟩
        incrB n + ms + ms * n
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        (one ∷ []) + *2 ms + (n + ms * n)
    ≡⟨ cong (λ x → x + (n + ms * n)) (sym (split-∷ one ms)) ⟩
        (one ∷ ms) + (n + ms * n)
    ∎
+B-*B-incrB (two ∷ ms) n =
    begin
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!    !}
    ∎
-}
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
