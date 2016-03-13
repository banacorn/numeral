module Data.Num.Bijective.Properties where

open import Data.Num.Bijective

open import Data.Nat
open import Data.Fin as Fin using (Fin)
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as PropEq
    hiding ([_])
open ≡-Reasoning

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

toℕ-injective : ∀ b → (xs ys : Num (suc b)) → toℕ xs ≡ toℕ ys → xs ≡ ys
toℕ-injective b ∙ ∙ prop = refl
toℕ-injective b ∙ ([ x ] ys) ()
toℕ-injective b ([ x ] xs) ∙ ()
toℕ-injective b ([ x ] xs) ([ y ] ys) prop =
    cong₂ [_]_ (proj₁ ind) (toℕ-injective b xs ys (proj₂ ind))
    where
            open import Data.Fin.Properties.Extra
            open import Data.Nat.Properties.Extra as ℕProp
            ind : x ≡ y × toℕ xs ≡ toℕ ys
            ind = some-lemma b x y (toℕ xs) (toℕ ys) (ℕProp.suc-injective prop)

--
--      xs ── +1 ──➞ xs'
--      |              |
--     toℕ           toℕ
--      ↓              ↓
--      n ── suc ─➞ suc n
--
+1-toℕ-suc : ∀ b xs → toℕ {suc b} (+1 xs) ≡ suc (toℕ xs)
+1-toℕ-suc b ∙ = refl
+1-toℕ-suc b ([ x ] xs) with Fin.toℕ x ≟ b
+1-toℕ-suc b ([ x ] xs) | yes p =
    begin
        toℕ ([ Fin.zero ] +1 xs)
    ≡⟨ cong (λ w → suc (w * suc b)) (+1-toℕ-suc b xs) ⟩
        suc (suc (b + toℕ xs * suc b))
    ≡⟨ cong (λ w → suc (suc (w + toℕ xs * suc b))) (sym p) ⟩
        suc (toℕ ([ x ] xs))
    ∎
+1-toℕ-suc b ([ x ] xs) | no ¬p =
    cong (λ w → suc w + toℕ xs * suc b) (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p)))
    where   open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)
+1-never-∙ : ∀ {b} xs → +1 {b} xs ≢ ∙
+1-never-∙ ∙ ()
+1-never-∙ {b} ([ x ] xs) +1xs≡∙ with Fin.toℕ x ≟ b
+1-never-∙ ([ x ] xs) () | yes p
+1-never-∙ ([ x ] xs) () | no ¬p

fromℕ-∙-0 : ∀ {b} n → fromℕ {b} n ≡ ∙ → n ≡ 0
fromℕ-∙-0 zero    p = refl
fromℕ-∙-0 (suc n) p = contradiction p (+1-never-∙ (fromℕ n))
    where   open import Relation.Nullary.Negation

toℕ-∙-0 : ∀ {b} xs → toℕ {suc b} xs ≡ 0 → xs ≡ ∙
toℕ-∙-0 ∙ p = refl
toℕ-∙-0 ([ x ] xs) ()


--
--      n ── fromℕ ─➞ xs ── toℕ ─➞ n
--


toℕ-fromℕ : ∀ b n → toℕ {suc b} (fromℕ {b} n) ≡ n
toℕ-fromℕ b zero = refl
toℕ-fromℕ b (suc n)  with fromℕ {b} n | inspect (fromℕ {b}) n
toℕ-fromℕ b (suc n) | ∙ | PropEq.[ eq ] = cong suc (sym (fromℕ-∙-0 n eq))
toℕ-fromℕ b (suc n) | [ x ] xs | PropEq.[ eq ] with Fin.toℕ x ≟ b
toℕ-fromℕ b (suc n) | [ x ] xs | PropEq.[ eq ] | yes p =
    begin
        toℕ ([ Fin.zero ] +1 xs)
    ≡⟨ refl ⟩
        suc (toℕ (+1 xs) * suc b)
    ≡⟨ cong (λ w → suc (w * suc b)) (+1-toℕ-suc b xs) ⟩
        suc (suc (b + toℕ xs * suc b))
    ≡⟨ cong (λ w → suc (suc (w + toℕ xs * suc b))) (sym p) ⟩
        suc (suc (Fin.toℕ x) + toℕ xs * suc b)
    ≡⟨ cong (λ w → suc (toℕ w)) (sym eq) ⟩
        suc (toℕ (fromℕ n))
    ≡⟨ cong suc (toℕ-fromℕ b n) ⟩
        suc n
    ∎
toℕ-fromℕ b (suc n) | [ x ] xs | PropEq.[ eq ] | no ¬p =
    begin
        toℕ ([ digit+1 x ¬p ] xs)
    ≡⟨ cong (λ w → suc (w + toℕ xs * suc b)) (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p))) ⟩
        suc (suc (Fin.toℕ x + toℕ xs * suc b))
    ≡⟨ cong (λ w → suc (toℕ w)) (sym eq) ⟩
        suc (toℕ (fromℕ n))
    ≡⟨ cong suc (toℕ-fromℕ b n) ⟩
        suc n
    ∎
    where   open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)


--
--      ns  ──  .....  ─➞ toℕ x + toℕ xs * base
--      |                    |
--    fromℕ                fromℕ
--      ↓                    ↓
--      xs ── [ x ]_ ──➞ [ x ] xs
--
-- +1-toℕ-suc : ∀ b xs → toℕ {suc b} (+1 xs) ≡ suc (toℕ xs)
*+-[]-coherence : ∀ b ns n → fromℕ ((suc n) + ns * suc b) ≡ ([ Fin.fromℕ n ] (fromℕ ns))
*+-[]-coherence b ns n = {! ns  !}

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

-- b ≡ 1 →             base = 2
-- x = 0 → Fin.suc x → digit = 2

raise-base : ∀ b → Num (suc b) → Num (suc (suc b))
raise-base b ∙ = ∙
raise-base b ([ x ] xs) = [ Fin.inject₁ x ] raise-base b xs

-- it's-ok-to-raise-base : ∀ b xs → toℕ xs ≡ toℕ (raise-base xs) → xs ≡ raise-base xs

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

digit-toℕ-inject₁-base : ∀ b
    → (x : Fin (suc b))
    → digit-toℕ {suc b} x ≡ digit-toℕ {suc (suc b)} (Fin.inject₁ x)
digit-toℕ-inject₁-base b Fin.zero = refl
digit-toℕ-inject₁-base b (Fin.suc x) = cong (suc ∘ suc) (sym (inject₁-lemma x))
    where   open import Data.Fin.Properties



-- digit-toℕ-reduce₁-base : ∀ b
--     → (x : Fin (suc b))
--     → Fin.toℕ x ≢ suc b
--     → digit-toℕ {suc b} x ≡ digit-toℕ {b} x
-- digit-toℕ-reduce₁-base = ?
-- fromℕ-digit-toℕ-raise-base : ∀ b
--     → (x : Fin (suc (b)))
--     → fromℕ {b} (digit-toℕ {suc b} x) ≡ {! raise-base  !}
-- fromℕ-digit-toℕ-raise-base = {!   !}

lemma : ∀ b x xs
      → fromℕ {b} (digit-toℕ x + toℕ {suc b} xs * suc b) ≡ ([ x ] xs)
lemma b Fin.zero    ∙ = refl
lemma zero (Fin.suc ()) ∙
-- lemma (suc b) (Fin.suc x) ∙ with Fin.toℕ (Fin.inject₁ x) ≟ suc b
lemma (suc b) (Fin.suc x) ∙ =
--     begin
--         +1 (fromℕ (digit-toℕ {suc b} x + zero))
--     ≡⟨ cong +1 {!    !} ⟩
--         +1 {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ∎
    begin
        +1 (fromℕ (digit-toℕ {suc b} x + 0))
    ≡⟨ cong (λ w → +1 (fromℕ (w + zero))) (digit-toℕ-inject₁-base b x) ⟩
        +1 (fromℕ (digit-toℕ {suc (suc b)} (Fin.inject₁ x) + 0))
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    -- ≡⟨ cong +1 (lemma (suc b) (Fin.inject₁ x) ∙) ⟩
    --     +1 ([ Fin.inject₁ x ] ∙)
    ≡⟨ {!   !} ⟩
        ( [ Fin.suc x ] ∙  )
    ∎
    where
            open import Data.Fin.Properties
            lemma1 : ∀ x → fromℕ (digit-toℕ {suc (suc b)} (Fin.inject₁ x) + 0) ≡ raise-base b (fromℕ (digit-toℕ {suc b} x + 0))
            lemma1 Fin.zero = refl
            lemma1 (Fin.suc x) =
                begin
                    +1 (+1 (fromℕ (Fin.toℕ (Fin.inject₁ x) + zero)))
                ≡⟨ cong (λ w → +1 (+1 (fromℕ (w + zero)))) (inject₁-lemma x) ⟩
                    +1 (+1 (fromℕ (Fin.toℕ x + zero)))
                ≡⟨ {!   !} ⟩
                    {!   !}
                ≡⟨ {!   !} ⟩
                    {!   !}
                ≡⟨ refl ⟩
                    raise-base b (+1 (+1 (fromℕ (Fin.toℕ x + zero))))
                ∎


lemma b x ([ x' ] xs') =
    begin
        fromℕ (suc (Fin.toℕ x) + toℕ ([ x' ] xs') * suc b)
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        ( [ x ] [ x' ] xs'   )
    ∎


-- fromℕ-toℕ : ∀ b xs → fromℕ {b} (toℕ {suc b} xs) ≡ xs
-- fromℕ-toℕ b ∙ = refl
-- fromℕ-toℕ b ([ x ] xs) with fromℕ {b} (Fin.toℕ x + toℕ xs * suc b) | inspect (fromℕ {b}) (Fin.toℕ x + toℕ xs * suc b)
-- fromℕ-toℕ b ([ x ] xs) | ∙ | PropEq.[ eq ] = {!   !}
-- fromℕ-toℕ b ([ x ] xs) | [ x' ] xs' | PropEq.[ eq ] with Fin.toℕ x' ≟ b
-- fromℕ-toℕ b ([ Fin.zero ] xs) | [ x' ] xs' | PropEq.[ eq ] | yes p = cong (λ w → [ Fin.zero ] w) $
--     begin
--         +1 xs'
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         xs
--     ∎
-- fromℕ-toℕ b ([ Fin.suc x ] xs) | [ x' ] xs' | PropEq.[ eq ] | yes p =
--     begin
--         ([ Fin.zero ] +1 xs')
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         ([ Fin.suc x ] xs)
--     ∎



    -- begin
    --     ([ Fin.zero ] +1 xs')
    -- ≡⟨ {!    !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     ([ Fin.suc x ] xs)
    -- ∎
    -- where   0≡x : Fin.zero ≡ x
    --         0≡x = {!   !}
-- fromℕ-toℕ b ([ x ] xs) | [ x' ] xs' | PropEq.[ eq ] | no ¬p = {!   !}
    -- begin
    -- {!   !}
    -- ≡⟨ {!   !} ⟩
    -- {!   !}
    -- ≡⟨ {!   !} ⟩
    -- {!   !}
    -- ≡⟨ {!   !} ⟩
    -- {!   !}
    -- ≡⟨ {!   !} ⟩
    -- {!   !}
    -- ∎




-- fromℕ-toℕ : ∀ b xs → fromℕ {b} (toℕ {suc b} xs) ≡ xs
-- fromℕ-toℕ b ∙ = refl
-- fromℕ-toℕ b ([ x ] xs) with Fin.toℕ x + toℕ xs * suc b | inspect (λ x → Fin.toℕ x + toℕ xs * suc b) x
-- fromℕ-toℕ b ([ x ] xs) | zero | PropEq.[ eq ] =
--     begin
--         ([ Fin.zero ] ∙)
--     ≡⟨ cong₂ [_]_ 0≡x ∙≡xs ⟩
--         ([ x ] xs)
--     ∎
--     where   open import Data.Nat.Properties
--             open import Data.Fin.Properties
--             open import Data.Sum
--             0≡x : Fin.zero ≡ x
--             0≡x = toℕ-injective (sym (i+j≡0⇒i≡0 (Fin.toℕ x) eq))
--             A⊎B,¬B⇒A : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → ¬ B → A
--             A⊎B,¬B⇒A (inj₁ a) ¬b = a
--             A⊎B,¬B⇒A (inj₂ b) ¬b = contradiction b ¬b
--             ∙≡xs : ∙ ≡ xs
--             ∙≡xs = sym (toℕ-∙-0 xs (A⊎B,¬B⇒A (i*j≡0⇒i≡0∨j≡0 (toℕ xs) (i+j≡0⇒j≡0 (Fin.toℕ x) eq)) (λ ())))
--
-- fromℕ-toℕ b ([ x ] xs) | suc n | PropEq.[ eq ] =
--     begin
--         +1 (+1 (fromℕ n))
--     ≡⟨ refl ⟩
--         +1 (fromℕ (suc n))
--     ≡⟨ refl ⟩
--         fromℕ (suc (suc n))
--     ≡⟨ cong (λ w → fromℕ (suc w)) (sym eq) ⟩
--         fromℕ (suc (Fin.toℕ x + toℕ xs * suc b))
--     ≡⟨ refl ⟩
--         fromℕ (suc (Fin.toℕ x) + toℕ xs * suc b)
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         ( [ x ] xs  )
--     ∎


--
-- open import Data.Nat.DivMod
-- open import Data.Nat.Properties.Simple
--
-- add-comm : ∀ {b} → (xs ys : Num b) → add xs ys ≡ add ys xs
-- add-comm ∙          ∙ = refl
-- add-comm ∙          ([ y ] ys) = refl
-- add-comm ([ x ] xs) ∙ = refl
-- add-comm {zero} ([ () ] xs) ([ () ] ys)
-- add-comm {suc b} ([ x ] xs) ([ y ] ys) with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b) | (suc (Fin.toℕ y + Fin.toℕ x)) divMod (suc b)
-- add-comm {suc b} ([ x ] xs) ([ y ] ys) | result zero R prop | result zero R' prop' =
--     begin
--         ([ R ] add xs ys)
--     ≡⟨ cong (λ w → [ w ] add xs ys) (toℕ-injective (
--         begin
--             Fin.toℕ R
--         ≡⟨ sym (+-right-identity (Fin.toℕ R)) ⟩
--             Fin.toℕ R + zero
--         ≡⟨ sym prop ⟩
--             suc (Fin.toℕ x + Fin.toℕ y)
--         ≡⟨ cong suc (+-comm (Fin.toℕ x) (Fin.toℕ y)) ⟩
--             suc (Fin.toℕ y + Fin.toℕ x)
--         ≡⟨ prop' ⟩
--             Fin.toℕ R' + zero
--         ≡⟨ +-right-identity (Fin.toℕ R') ⟩
--             Fin.toℕ R'
--         ∎
--     ))⟩
--         ([ R' ] add xs ys)
--     ≡⟨ cong (λ w → [ R' ] w) (add-comm {suc b} xs ys) ⟩
--         ([ R' ] add ys xs)
--     ∎
-- add-comm {suc b} ([ x ] xs) ([ y ] ys) | result zero R prop | result (suc Q') R' prop' = {!   !}
-- add-comm {suc b} ([ x ] xs) ([ y ] ys) | result (suc Q) R prop | result Q' R' prop' = {!   !}
-- -- add-comm {suc b} ([ x ] xs) ([ y ] ys) with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b)
-- -- add-comm {suc b} ([ x ] xs) ([ y ] ys) | result zero R prop =
-- --     begin
-- --         add ([ x ] xs) ([ y ] ys)
-- --     ≡⟨ refl ⟩
-- --         add ([ x ] xs) ([ y ] ys)
-- --     ≡⟨ refl ⟩
-- --         add ([ x ] xs) ([ y ] ys)
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         add ([ y ] ys) ([ x ] xs)
-- --     ∎
-- -- add-comm ([ x ] xs) ([ y ] ys) | result (suc Q) R prop = {!   !}
-- --     -- where
