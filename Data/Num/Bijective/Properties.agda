module Data.Num.Bijective.Properties where

open import Data.Num.Bijective

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Fin as Fin using (Fin)
open import Data.Product
open import Function
open import Function.Injection hiding (_∘_)
open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as PropEq
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

∷-injective : ∀ {b}
    → {x y : Fin (suc b)}
    → {xs ys : Num (suc b)}
    → x ∷ xs ≡ y ∷ ys
    → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

1+-never-∙ : ∀ {b} xs → 1+ {b} xs ≢ ∙
1+-never-∙     ∙        ()
1+-never-∙ {b} (x ∷ xs) +1xs≡∙ with full x
1+-never-∙     (x ∷ xs) () | yes p
1+-never-∙     (x ∷ xs) () | no ¬p

digit+1-never-0 : ∀ {b} (x : Fin (suc b)) → (¬p : Fin.toℕ x ≢ b) → digit+1 x ¬p ≢ Fin.zero
digit+1-never-0 {b}     x            ¬p eq with Fin.toℕ x ≟ b
digit+1-never-0 {b}     x            ¬p eq | yes q = contradiction q ¬p
digit+1-never-0 {zero}  Fin.zero     ¬p eq | no ¬q = contradiction refl ¬p
digit+1-never-0 {suc b} Fin.zero     ¬p eq | no ¬q = contradiction eq (λ ())
digit+1-never-0 {zero}  (Fin.suc ()) ¬p eq | no ¬q
digit+1-never-0 {suc b} (Fin.suc x)  ¬p () | no ¬q

digit+1-injective :  ∀ {b} (x y : Fin (suc b))
    → (¬p : Fin.toℕ x ≢ b)
    → (¬q : Fin.toℕ y ≢ b)
    → digit+1 x ¬p ≡ digit+1 y ¬q
    → x ≡ y
digit+1-injective         Fin.zero     Fin.zero     ¬p ¬q eq = refl
digit+1-injective {zero}  Fin.zero     (Fin.suc ()) ¬p ¬q eq
digit+1-injective {suc b} Fin.zero     (Fin.suc y)  ¬p ¬q eq = toℕ-injective (suc-injective eq')
    where   open import Data.Fin.Properties
            open import Data.Nat.Properties.Extra
            eq' : Fin.toℕ {suc (suc b)} (digit+1 Fin.zero ¬p) ≡ suc (Fin.toℕ {suc (suc b)} (Fin.suc y))
            eq' = begin
                    Fin.toℕ {suc (suc b)} (Fin.suc Fin.zero)
                ≡⟨ cong Fin.toℕ eq ⟩
                    suc (Fin.toℕ (Fin.fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ y) b (bounded y) (¬q ∘ cong suc)))))
                ≡⟨ cong suc (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ y) b (bounded y) (¬q ∘ cong suc)))) ⟩
                    suc (Fin.toℕ {suc (suc b)} (Fin.suc y))
                ∎
digit+1-injective {zero}  (Fin.suc ()) Fin.zero    ¬p ¬q eq
digit+1-injective {suc b} (Fin.suc x)  Fin.zero    ¬p ¬q eq = toℕ-injective (suc-injective eq')
    where   open import Data.Fin.Properties
            open import Data.Nat.Properties.Extra
            eq' : suc (Fin.toℕ {suc (suc b)} (Fin.suc x)) ≡ Fin.toℕ {suc (suc b)} (digit+1 Fin.zero ¬q)
            eq' = begin
                    suc (Fin.toℕ {suc (suc b)} (Fin.suc x))
                ≡⟨ cong suc (sym (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) (¬p ∘ cong suc))))) ⟩
                    suc (Fin.toℕ (Fin.fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) (¬p ∘ cong suc)))))
                ≡⟨ cong Fin.toℕ eq ⟩
                    Fin.toℕ {suc (suc b)} (Fin.suc Fin.zero)
                ∎
digit+1-injective {zero}  (Fin.suc ()) (Fin.suc y) ¬p ¬q eq
digit+1-injective {suc b} (Fin.suc x)  (Fin.suc y) ¬p ¬q eq = cong Fin.suc (digit+1-injective x y (¬p ∘ cong suc) (¬q ∘ cong suc) (suc-injective eq))
    where   open import Data.Fin.Properties.Extra

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
1+-injective : ∀ b → (xs ys : Num (suc b)) → 1+ xs ≡ 1+ ys → xs ≡ ys
1+-injective b ∙        ∙        eq = refl
1+-injective b ∙        (y ∷ ys) eq with full y
1+-injective b ∙        (y ∷ ys) eq | yes p = contradiction (proj₂ (∷-injective (sym eq))) (1+-never-∙ ys)
1+-injective b ∙        (y ∷ ys) eq | no ¬p = contradiction (proj₁ (∷-injective (sym eq))) (digit+1-never-0 y ¬p)
1+-injective b (x ∷ xs) ∙        eq with full x
1+-injective b (x ∷ xs) ∙        eq | yes p = contradiction (proj₂ (∷-injective eq)) (1+-never-∙ xs)
1+-injective b (x ∷ xs) ∙        eq | no ¬p = contradiction (proj₁ (∷-injective eq)) (digit+1-never-0 x ¬p)
1+-injective b (x ∷ xs) (y ∷ ys) eq with full x | full y
1+-injective b (x ∷ xs) (y ∷ ys) eq | yes p | yes q = cong₂ _∷_ x≡y xs≡ys
    where   open import Data.Fin.Properties
            x≡y : x ≡ y
            x≡y = toℕ-injective (trans p (sym q))
            xs≡ys : xs ≡ ys
            xs≡ys = 1+-injective b xs ys (proj₂ (∷-injective eq))
1+-injective b (x ∷ xs) (y ∷ ys) eq | yes p | no ¬q = contradiction (sym (proj₁ (∷-injective eq))) (digit+1-never-0 y ¬q)
1+-injective b (x ∷ xs) (y ∷ ys) eq | no ¬p | yes q = contradiction (proj₁ (∷-injective eq))       (digit+1-never-0 x ¬p)
1+-injective b (x ∷ xs) (y ∷ ys) eq | no ¬p | no ¬q = cong₂ _∷_ (digit+1-injective x y ¬p ¬q (proj₁ (∷-injective eq))) (proj₂ (∷-injective eq))


toℕ-injective : ∀ b → (xs ys : Num (suc b)) → toℕ xs ≡ toℕ ys → xs ≡ ys
toℕ-injective b ∙        ∙        eq = refl
toℕ-injective b ∙        (y ∷ ys) ()
toℕ-injective b (x ∷ xs) ∙        ()
toℕ-injective b (x ∷ xs) (y ∷ ys) eq =
    cong₂ _∷_ (proj₁ ind) (toℕ-injective b xs ys (proj₂ ind))
    where
            open import Data.Fin.Properties.Extra
            open import Data.Nat.Properties.Extra as ℕProp
            ind : x ≡ y × toℕ xs ≡ toℕ ys
            ind = some-lemma b x y (toℕ xs) (toℕ ys) (ℕProp.suc-injective eq)

fromℕ-injective : ∀ b m n → fromℕ {b} m ≡ fromℕ {b} n → m ≡ n
fromℕ-injective b zero    zero    eq = refl
fromℕ-injective b zero    (suc n) eq = contradiction (sym eq) (1+-never-∙ (fromℕ n))
fromℕ-injective b (suc m) zero    eq = contradiction eq       (1+-never-∙ (fromℕ m))
fromℕ-injective b (suc m) (suc n) eq = cong suc (fromℕ-injective b m n (1+-injective b (fromℕ m) (fromℕ n) eq))

--
--      xs ── 1+ ──➞ xs'
--      |              |
--     toℕ           toℕ
--      ↓              ↓
--      n ── suc ─➞ suc n
--
toℕ-1+ : ∀ b xs → toℕ {suc b} (1+ xs) ≡ suc (toℕ xs)
toℕ-1+ b ∙        = refl
toℕ-1+ b (x ∷ xs) with full x
toℕ-1+ b (x ∷ xs) | yes p =
    begin
        toℕ (Fin.zero ∷ 1+ xs)
    ≡⟨ cong (λ w → suc (w * suc b)) (toℕ-1+ b xs) ⟩
        suc (suc (b + toℕ xs * suc b))
    ≡⟨ cong (λ w → suc (suc (w + toℕ xs * suc b))) (sym p) ⟩
        suc (toℕ (x ∷ xs))
    ∎
toℕ-1+ b (x ∷ xs) | no ¬p =
    cong (λ w → suc w + toℕ xs * suc b) (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p)))
    where   open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)

--
--      xs ── n+ n ──➞ n+ n xs
--      |                  |
--     toℕ               toℕ
--      ↓                  ↓
--      m ──   n + ──➞ n + m
--

toℕ-n+ : ∀ b n xs → toℕ {suc b} (n+ n xs) ≡ n + (toℕ xs)
toℕ-n+ b zero xs = refl
toℕ-n+ b (suc n) xs = begin
        toℕ (1+ (n+ n xs))
    ≡⟨ toℕ-1+ b (n+ n xs) ⟩
        suc (toℕ (n+ n xs))
    ≡⟨ cong suc (toℕ-n+ b n xs) ⟩
        suc (n + toℕ xs)
    ∎

fromℕ-∙-0 : ∀ {b} n → fromℕ {b} n ≡ ∙ → n ≡ 0
fromℕ-∙-0 zero    p = refl
fromℕ-∙-0 (suc n) p = contradiction p (1+-never-∙ (fromℕ n))
    where   open import Relation.Nullary.Negation

toℕ-∙-0 : ∀ {b} xs → toℕ {suc b} xs ≡ 0 → xs ≡ ∙
toℕ-∙-0 ∙ p = refl
toℕ-∙-0 (x ∷ xs) ()


--
--      n ── fromℕ ─➞ xs ── toℕ ─➞ n
--


toℕ-fromℕ : ∀ b n → toℕ {suc b} (fromℕ {b} n) ≡ n
toℕ-fromℕ b zero    = refl
toℕ-fromℕ b (suc n) with fromℕ {b} n | inspect (fromℕ {b}) n
toℕ-fromℕ b (suc n) | ∙      | [ eq ] = cong suc (sym (fromℕ-∙-0 n eq))
toℕ-fromℕ b (suc n) | x ∷ xs | [ eq ] with full x
toℕ-fromℕ b (suc n) | x ∷ xs | [ eq ] | yes p =
    begin
        toℕ (Fin.zero ∷ 1+ xs)
    ≡⟨ refl ⟩
        suc (toℕ (1+ xs) * suc b)
    ≡⟨ cong (λ w → suc (w * suc b)) (toℕ-1+ b xs) ⟩
        suc (suc (b + toℕ xs * suc b))
    ≡⟨ cong (λ w → suc (suc (w + toℕ xs * suc b))) (sym p) ⟩
        suc (suc (Fin.toℕ x) + toℕ xs * suc b)
    ≡⟨ cong (λ w → suc (toℕ w)) (sym eq) ⟩
        suc (toℕ (fromℕ n))
    ≡⟨ cong suc (toℕ-fromℕ b n) ⟩
        suc n
    ∎
toℕ-fromℕ b (suc n) | x ∷ xs | [ eq ] | no ¬p =
    begin
        toℕ (digit+1 x ¬p ∷ xs)
    ≡⟨ cong (λ w → suc (w + toℕ xs * suc b)) (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p))) ⟩
        suc (suc (Fin.toℕ x + toℕ xs * suc b))
    ≡⟨ cong (λ w → suc (toℕ w)) (sym eq) ⟩
        suc (toℕ (fromℕ n))
    ≡⟨ cong suc (toℕ-fromℕ b n) ⟩
        suc n
    ∎
    where   open import Data.Fin.Properties using (toℕ-fromℕ≤; bounded)


toℕ-fromℕ-inverse : ∀ b {m} {n} → toℕ (fromℕ {b} m) ≡ n → m ≡ n
toℕ-fromℕ-inverse b {m} {n} eq =
    begin
        m
    ≡⟨ sym (toℕ-fromℕ b m) ⟩
        toℕ (fromℕ m)
    ≡⟨ eq ⟩
        n
    ∎


--
--      ns  ──  .....  ─➞ toℕ x + toℕ xs * base
--      |                    |
--    fromℕ                fromℕ
--      ↓                    ↓
--      xs ── [ x ]_ ──➞ x ∷ xs
--
-- toℕ-1+ : ∀ b xs → toℕ {suc b} (1+ xs) ≡ suc (toℕ xs)
-- *+-[]-coherence : ∀ b ns n → fromℕ ((suc n) + ns * suc b) ≡ Fin.fromℕ n ∷ (fromℕ ns)
-- *+-[]-coherence b ns n = {! ns  !}

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

-- raise-base : ∀ b → Num (suc b) → Num (suc (suc b))
-- raise-base b ∙        = ∙
-- raise-base b (x ∷ xs) = Fin.inject₁ x ∷ raise-base b xs

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


-- induction on "increase-base-primitive b xs", to avoid having to use fromℕ-toℕ

-- old base = suc b
-- new base = suc (suc b)
increase-base-primitive : ∀ b
    → (xs : Num (suc b))
    → Σ[ ys ∈ Num (suc (suc b)) ] toℕ xs ≡ toℕ ys
increase-base-primitive b ∙ = ∙ , refl
increase-base-primitive b (x ∷ xs) with fromℕ {suc b} (toℕ (proj₁ (increase-base-primitive b xs)) * suc b) | inspect (λ ws → fromℕ {suc b} (toℕ ws * suc b)) (proj₁ (increase-base-primitive b xs))
increase-base-primitive b (x ∷ xs) | ∙ | [ eq ] = (Fin.inject₁ x ∷ ∙) , proof
    where   open import Data.Fin.Properties

            eq' : toℕ (proj₁ (increase-base-primitive b xs)) * suc b ≡ 0
            eq' = toℕ-fromℕ-inverse (suc b) (cong toℕ eq)

            proof : suc (Fin.toℕ x + toℕ xs * suc b) ≡ suc (Fin.toℕ (Fin.inject₁ x) + 0)
            proof = cong suc $ begin
                    Fin.toℕ x + toℕ xs * suc b
                ≡⟨ cong (λ w → Fin.toℕ x + w * suc b) (proj₂ (increase-base-primitive b xs)) ⟩
                    Fin.toℕ x + toℕ (proj₁ (increase-base-primitive b xs)) * suc b
                ≡⟨ cong (λ w → Fin.toℕ x + w) eq' ⟩
                    Fin.toℕ x + 0
                ≡⟨ cong (λ w → w + 0) (sym (inject₁-lemma x)) ⟩
                    Fin.toℕ (Fin.inject₁ x) + 0
                ∎
increase-base-primitive b (x ∷ xs) | y ∷ ys | [ eq ] with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc (suc b))
increase-base-primitive b (x ∷ xs) | y ∷ ys | [ eq ] | result quotient remainder property =
    (remainder ∷ n+ quotient ys) , proof
    where   open import Data.Fin.Properties
            open import Data.Nat.Properties.Simple

            eq' : toℕ (proj₁ (increase-base-primitive b xs)) * suc b ≡ toℕ (y ∷ ys)
            eq' = toℕ-fromℕ-inverse (suc b) (cong toℕ eq)

            proof : suc (Fin.toℕ x + toℕ xs * suc b) ≡ suc (Fin.toℕ remainder + toℕ (n+ quotient ys) * suc (suc b))
            proof = cong suc $ begin
                    Fin.toℕ x + toℕ xs * suc b
                ≡⟨ cong (λ w → Fin.toℕ x + w * suc b) (proj₂ (increase-base-primitive b xs)) ⟩
                    Fin.toℕ x + toℕ (proj₁ (increase-base-primitive b xs)) * suc b
                ≡⟨ cong (λ w → Fin.toℕ x + w) eq' ⟩
                    Fin.toℕ x + toℕ (y ∷ ys)
                ≡⟨ +-suc (Fin.toℕ x) (Fin.toℕ y + toℕ ys * suc (suc b)) ⟩
                    suc (Fin.toℕ x + (Fin.toℕ y + toℕ ys * suc (suc b)))
                ≡⟨ cong suc (sym (+-assoc (Fin.toℕ x) (Fin.toℕ y) (toℕ ys * suc (suc b)))) ⟩
                    suc (Fin.toℕ x + Fin.toℕ y + toℕ ys * suc (suc b))
                ≡⟨ cong (λ w → w + toℕ ys * suc (suc b)) property ⟩
                    Fin.toℕ remainder + quotient * suc (suc b) + toℕ ys * suc (suc b)
                ≡⟨ +-assoc (Fin.toℕ remainder) (quotient * suc (suc b)) (toℕ ys * suc (suc b)) ⟩
                    Fin.toℕ remainder + (quotient * suc (suc b) + toℕ ys * suc (suc b))
                ≡⟨ cong (λ w → Fin.toℕ remainder + w) (sym (distribʳ-*-+ (suc (suc b)) quotient (toℕ ys))) ⟩
                    Fin.toℕ remainder + (quotient + toℕ ys) * suc (suc b)
                ≡⟨ cong (λ w → Fin.toℕ remainder + w * suc (suc b)) (sym (toℕ-n+ (suc b) quotient ys)) ⟩
                    Fin.toℕ remainder + toℕ (n+ quotient ys) * suc (suc b)
                ∎

increase-base : ∀ {b} → Num (suc b) → Num (suc (suc b))
increase-base {b} xs = proj₁ (increase-base-primitive b xs)

increase-base-lemma : ∀ {b} → (xs : Num (suc b)) → toℕ (increase-base xs) ≡ toℕ xs
increase-base-lemma {b} xs = sym (proj₂ (increase-base-primitive b xs))

-- old base = suc (suc b)
-- new base = suc b
decrease-base-primitive : ∀ b
    → (xs : Num (suc (suc b)))
    → Σ[ ys ∈ Num (suc b) ] toℕ xs ≡ toℕ ys
decrease-base-primitive b ∙ = ∙ , refl
decrease-base-primitive b (x ∷ xs) with fromℕ {b} (toℕ (proj₁ (decrease-base-primitive b xs)) * suc (suc b)) | inspect (λ ws → fromℕ {b} (toℕ ws * suc (suc b))) (proj₁ (decrease-base-primitive b xs))
decrease-base-primitive b (x ∷ xs) | ∙      | [ eq ] with full x
decrease-base-primitive b (x ∷ xs) | ∙      | [ eq ] | yes p =
    (Fin.zero ∷ Fin.zero ∷ ∙) , proof
    where   proof : suc (Fin.toℕ x + toℕ xs * suc (suc b)) ≡ suc (suc (b + 0))
            proof = cong suc $ begin
                    Fin.toℕ x + toℕ xs * suc (suc b)
                ≡⟨ cong (λ w → Fin.toℕ x + w * suc (suc b)) (proj₂ (decrease-base-primitive b xs)) ⟩
                    Fin.toℕ x + toℕ (proj₁ (decrease-base-primitive b xs)) * suc (suc b)
                ≡⟨ cong (λ w → Fin.toℕ x + w) (toℕ-fromℕ-inverse b (cong toℕ eq)) ⟩
                    Fin.toℕ x + 0
                ≡⟨ cong (λ w → w + 0) p ⟩
                    suc (b + 0)
                ∎
decrease-base-primitive b (x ∷ xs) | ∙      | [ eq ] | no ¬p =
    inject-1 x ¬p ∷ ∙ , proof
    where   open import Data.Fin.Properties
            open import Data.Fin.Properties.Extra
            proof : suc (Fin.toℕ x + toℕ xs * suc (suc b)) ≡ suc (Fin.toℕ (inject-1 x ¬p) + 0)
            proof = cong suc $ begin
                    Fin.toℕ x + toℕ xs * suc (suc b)
                ≡⟨ cong (λ w → Fin.toℕ x + w * suc (suc b)) (proj₂ (decrease-base-primitive b xs)) ⟩
                    Fin.toℕ x + toℕ (proj₁ (decrease-base-primitive b xs)) * suc (suc b)
                ≡⟨ cong (λ w → Fin.toℕ x + w) (toℕ-fromℕ-inverse b {toℕ (proj₁ (decrease-base-primitive b xs)) * suc (suc b)} {0} (cong toℕ eq)) ⟩
                    Fin.toℕ x + zero
                ≡⟨ cong (λ w → w + 0) (sym (inject-1-lemma x ¬p)) ⟩
                    Fin.toℕ (inject-1 x ¬p) + 0
                ∎
decrease-base-primitive b (x ∷ xs) | y ∷ ys | [ eq ] with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b)
decrease-base-primitive b (x ∷ xs) | y ∷ ys | [ eq ] | result quotient remainder property =
    remainder ∷ n+ quotient ys , proof
    where   open import Data.Fin.Properties
            open import Data.Nat.Properties.Simple
            proof : suc (Fin.toℕ x + toℕ xs * suc (suc b)) ≡ suc (Fin.toℕ remainder + toℕ (n+ quotient ys) * suc b)
            proof = cong suc $
                begin
                    Fin.toℕ x + toℕ xs * suc (suc b)
                ≡⟨ cong (λ w → Fin.toℕ x + w * suc (suc b)) (proj₂ (decrease-base-primitive b xs)) ⟩
                    Fin.toℕ x + toℕ (proj₁ (decrease-base-primitive b xs)) * suc (suc b)
                ≡⟨ cong (λ w → Fin.toℕ x + w) (toℕ-fromℕ-inverse b (cong toℕ eq)) ⟩
                    Fin.toℕ x + (suc (Fin.toℕ y) + toℕ ys * suc b)
                ≡⟨ sym (+-assoc (Fin.toℕ x) (suc (Fin.toℕ y)) (toℕ ys * suc b)) ⟩
                    Fin.toℕ x + suc (Fin.toℕ y) + toℕ ys * suc b
                ≡⟨ cong (λ w → w + toℕ ys * suc b) (+-suc (Fin.toℕ x) (Fin.toℕ y)) ⟩
                    suc (Fin.toℕ x + Fin.toℕ y) + toℕ ys * suc b
                ≡⟨ cong (λ w → w + toℕ ys * suc b) property ⟩
                    Fin.toℕ remainder + quotient * suc b + toℕ ys * suc b
                ≡⟨ +-assoc (Fin.toℕ remainder) (quotient * suc b) (toℕ ys * suc b) ⟩
                    Fin.toℕ remainder + (quotient * suc b + toℕ ys * suc b)
                ≡⟨ cong (λ w → Fin.toℕ remainder + w) (sym (distribʳ-*-+ (suc b) quotient (toℕ ys))) ⟩
                    Fin.toℕ remainder + (quotient + toℕ ys) * suc b
                ≡⟨ cong (λ w → Fin.toℕ remainder + w * suc b) (sym (toℕ-n+ b quotient ys)) ⟩
                    Fin.toℕ remainder + toℕ (n+ quotient ys) * suc b
                ∎

decrease-base : ∀ {b} → Num (suc (suc b)) → Num (suc b)
decrease-base {b} xs = proj₁ (decrease-base-primitive b xs)

decrease-base-lemma : ∀ {b} → (xs : Num (suc (suc b))) → toℕ (decrease-base xs) ≡ toℕ xs
decrease-base-lemma {b} xs = sym (proj₂ (decrease-base-primitive b xs))

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

--
-- lemma : ∀ b x xs
--       → fromℕ {b} (digit-toℕ {suc b} x + toℕ {suc b} xs * suc b) ≡ x ∷ xs
-- lemma b        Fin.zero    ∙ = refl
-- lemma zero    (Fin.suc ()) ∙
-- lemma (suc b) (Fin.suc x)  ∙ =
--     begin
--         fromℕ {suc b} (digit-toℕ {suc (suc b)} (Fin.suc x) + 0)
--     ≡⟨ refl ⟩
--         1+ (fromℕ {suc b} (digit-toℕ {suc b} x + 0))
--     ≡⟨ cong (λ w → 1+ (fromℕ (w + 0))) (digit-toℕ-inject₁-base b x) ⟩
--         1+ (fromℕ {suc b} (digit-toℕ {suc (suc b)} (Fin.inject₁ x) + 0))
--     ≡⟨ refl ⟩
--         1+ (fromℕ {suc b} (suc (Fin.toℕ (Fin.inject₁ x)) + 0))
--     ≡⟨ cong (λ w → 1+ (fromℕ (suc w + 0))) (inject₁-lemma x) ⟩
--         1+ (fromℕ {suc b} (digit-toℕ {suc b} x + 0))
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         Fin.suc x ∷ ∙
--     ∎
--     where   open import Data.Fin.Properties
-- lemma b x (x' ∷ xs') =
--     begin
--         fromℕ (suc (Fin.toℕ x) + toℕ (x' ∷ xs') * suc b)
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         x ∷ x' ∷ xs'
--     ∎

-- fromℕ-toℕ : ∀ b xs → fromℕ {b} (toℕ {suc b} xs) ≡ xs
-- fromℕ-toℕ b xs = {!    !}


-- fromℕ-toℕ : ∀ b xs → fromℕ {b} (toℕ {suc b} xs) ≡ xs
-- fromℕ-toℕ b ∙ = refl
-- fromℕ-toℕ b (x ∷ xs) with fromℕ {b} (Fin.toℕ x + toℕ xs * suc b) | inspect (fromℕ {b}) (Fin.toℕ x + toℕ xs * suc b)
-- fromℕ-toℕ b (x ∷ xs) | ∙ | [ eq ] = {!   !}
-- fromℕ-toℕ b (x ∷ xs) | [ x' ] xs' | [ eq ] with Fin.toℕ x' ≟ b
-- fromℕ-toℕ b ([ Fin.zero ] xs) | [ x' ] xs' | [ eq ] | yes p = cong (λ w → [ Fin.zero ] w) $
--     begin
--         1+ xs'
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         xs
--     ∎
-- fromℕ-toℕ b ([ Fin.suc x ] xs) | [ x' ] xs' | [ eq ] | yes p =
--     begin
--         ([ Fin.zero ] 1+ xs')
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
    --     ([ Fin.zero ] 1+ xs')
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
-- fromℕ-toℕ b (x ∷ xs) | [ x' ] xs' | [ eq ] | no ¬p = {!   !}
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
-- fromℕ-toℕ b (x ∷ xs) with Fin.toℕ x + toℕ xs * suc b | inspect (λ x → Fin.toℕ x + toℕ xs * suc b) x
-- fromℕ-toℕ b (x ∷ xs) | zero | [ eq ] =
--     begin
--         ([ Fin.zero ] ∙)
--     ≡⟨ cong₂ [_]_ 0≡x ∙≡xs ⟩
--         (x ∷ xs)
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
-- fromℕ-toℕ b (x ∷ xs) | suc n | [ eq ] =
--     begin
--         1+ (1+ (fromℕ n))
--     ≡⟨ refl ⟩
--         1+ (fromℕ (suc n))
--     ≡⟨ refl ⟩
--         fromℕ (suc (suc n))
--     ≡⟨ cong (λ w → fromℕ (suc w)) (sym eq) ⟩
--         fromℕ (suc (Fin.toℕ x + toℕ xs * suc b))
--     ≡⟨ refl ⟩
--         fromℕ (suc (Fin.toℕ x) + toℕ xs * suc b)
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         ( x ∷ xs  )
--     ∎


--
-- open import Data.Nat.DivMod
-- open import Data.Nat.Properties.Simple
--
-- add-comm : ∀ {b} → (xs ys : Num b) → add xs ys ≡ add ys xs
-- add-comm ∙          ∙ = refl
-- add-comm ∙          (y ∷ ys) = refl
-- add-comm (x ∷ xs) ∙ = refl
-- add-comm {zero} ([ () ] xs) ([ () ] ys)
-- add-comm {suc b} (x ∷ xs) (y ∷ ys) with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b) | (suc (Fin.toℕ y + Fin.toℕ x)) divMod (suc b)
-- add-comm {suc b} (x ∷ xs) (y ∷ ys) | result zero R prop | result zero R' prop' =
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
-- add-comm {suc b} (x ∷ xs) (y ∷ ys) | result zero R prop | result (suc Q') R' prop' = {!   !}
-- add-comm {suc b} (x ∷ xs) (y ∷ ys) | result (suc Q) R prop | result Q' R' prop' = {!   !}
-- -- add-comm {suc b} (x ∷ xs) (y ∷ ys) with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b)
-- -- add-comm {suc b} (x ∷ xs) (y ∷ ys) | result zero R prop =
-- --     begin
-- --         add (x ∷ xs) (y ∷ ys)
-- --     ≡⟨ refl ⟩
-- --         add (x ∷ xs) (y ∷ ys)
-- --     ≡⟨ refl ⟩
-- --         add (x ∷ xs) (y ∷ ys)
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         {!   !}
-- --     ≡⟨ {!   !} ⟩
-- --         add (y ∷ ys) (x ∷ xs)
-- --     ∎
-- -- add-comm (x ∷ xs) (y ∷ ys) | result (suc Q) R prop = {!   !}
-- --     -- where
