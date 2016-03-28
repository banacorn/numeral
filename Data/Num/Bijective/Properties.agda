module Data.Num.Bijective.Properties where

open import Data.Num.Bijective

open import Data.Nat
open import Data.Nat.DM
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Fin                    as Fin using (Fin)
open import Data.Fin.Extra
open import Data.Fin.Properties         as FinP hiding (_≟_)
    renaming (toℕ-injective to Fin-toℕ-injective)
open import Data.Fin.Properties.Extra   as FinPX
    renaming (suc-injective to Fin-suc-injective)

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


------------------------------------------------------------------------
-- Various ≡-related lemmata
------------------------------------------------------------------------

1+-never-∙ : ∀ {b} xs → 1+ {b} xs ≢ ∙
1+-never-∙     ∙        ()
1+-never-∙ {b} (x ∷ xs) +1xs≡∙ with full x
1+-never-∙     (x ∷ xs) () | yes p
1+-never-∙     (x ∷ xs) () | no ¬p

fromℕ-∙-0 : ∀ {b} n → fromℕ {b} n ≡ ∙ → n ≡ 0
fromℕ-∙-0 zero    p = refl
fromℕ-∙-0 (suc n) p = contradiction p (1+-never-∙ (fromℕ n))

toℕ-∙-0 : ∀ {b} xs → toℕ {suc b} xs ≡ 0 → xs ≡ ∙
toℕ-∙-0 ∙ p = refl
toℕ-∙-0 (x ∷ xs) ()

digit+1-never-0 : ∀ {b} (x : Fin (suc b)) → (¬p : Fin.toℕ x ≢ b) → digit+1 x ¬p ≢ Fin.zero
digit+1-never-0 {b}     x            ¬p eq with Fin.toℕ x ≟ b
digit+1-never-0 {b}     x            ¬p eq | yes q = contradiction q ¬p
digit+1-never-0 {zero}  Fin.zero     ¬p eq | no ¬q = contradiction refl ¬p
digit+1-never-0 {suc b} Fin.zero     ¬p eq | no ¬q = contradiction eq (λ ())
digit+1-never-0 {zero}  (Fin.suc ()) ¬p eq | no ¬q
digit+1-never-0 {suc b} (Fin.suc x)  ¬p () | no ¬q

Fin⇒ℕ-digit+1 : ∀ {b}
    → (x : Fin (suc b))
    → (¬p : Fin.toℕ x ≢ b)
    → Fin.toℕ (digit+1 x ¬p) ≡ suc (Fin.toℕ x)
Fin⇒ℕ-digit+1 {b} x ¬p = toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) ¬p))

------------------------------------------------------------------------
-- injectivity
------------------------------------------------------------------------

∷-injective : ∀ {b}
    → {x y : Fin (suc b)}
    → {xs ys : Bij (suc b)}
    → x ∷ xs ≡ y ∷ ys
    → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

digit+1-injective :  ∀ {b} (x y : Fin (suc b))
    → (¬p : Fin.toℕ x ≢ b)
    → (¬q : Fin.toℕ y ≢ b)
    → digit+1 x ¬p ≡ digit+1 y ¬q
    → x ≡ y
digit+1-injective         Fin.zero     Fin.zero     ¬p ¬q eq = refl
digit+1-injective {zero}  Fin.zero     (Fin.suc ()) ¬p ¬q eq
digit+1-injective {suc b} Fin.zero     (Fin.suc y)  ¬p ¬q eq = Fin-toℕ-injective (suc-injective eq')
    where   eq' : Fin.toℕ {suc (suc b)} (digit+1 Fin.zero ¬p) ≡ suc (Fin.toℕ {suc (suc b)} (Fin.suc y))
            eq' = begin
                    Fin.toℕ {suc (suc b)} (Fin.suc Fin.zero)
                ≡⟨ cong Fin.toℕ eq ⟩
                    suc (Fin.toℕ (Fin.fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ y) b (bounded y) (¬q ∘ cong suc)))))
                ≡⟨ cong suc (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ y) b (bounded y) (¬q ∘ cong suc)))) ⟩
                    suc (Fin.toℕ {suc (suc b)} (Fin.suc y))
                ∎
digit+1-injective {zero}  (Fin.suc ()) Fin.zero    ¬p ¬q eq
digit+1-injective {suc b} (Fin.suc x)  Fin.zero    ¬p ¬q eq = Fin-toℕ-injective (suc-injective eq')
    where   eq' : suc (Fin.toℕ {suc (suc b)} (Fin.suc x)) ≡ Fin.toℕ {suc (suc b)} (digit+1 Fin.zero ¬q)
            eq' = begin
                    suc (Fin.toℕ {suc (suc b)} (Fin.suc x))
                ≡⟨ cong suc (sym (toℕ-fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) (¬p ∘ cong suc))))) ⟩
                    suc (Fin.toℕ (Fin.fromℕ≤ (s≤s (digit+1-lemma (Fin.toℕ x) b (bounded x) (¬p ∘ cong suc)))))
                ≡⟨ cong Fin.toℕ eq ⟩
                    Fin.toℕ {suc (suc b)} (Fin.suc Fin.zero)
                ∎
digit+1-injective {zero}  (Fin.suc ()) (Fin.suc y) ¬p ¬q eq
digit+1-injective {suc b} (Fin.suc x)  (Fin.suc y) ¬p ¬q eq = cong Fin.suc (digit+1-injective x y (¬p ∘ cong suc) (¬q ∘ cong suc) (Fin-suc-injective eq))
    where   open import Data.Fin.Properties.Extra

1+-injective : ∀ b → (xs ys : Bij (suc b)) → 1+ xs ≡ 1+ ys → xs ≡ ys
1+-injective b ∙        ∙        eq = refl
1+-injective b ∙        (y ∷ ys) eq with full y
1+-injective b ∙        (y ∷ ys) eq | yes p = contradiction (proj₂ (∷-injective (sym eq))) (1+-never-∙ ys)
1+-injective b ∙        (y ∷ ys) eq | no ¬p = contradiction (proj₁ (∷-injective (sym eq))) (digit+1-never-0 y ¬p)
1+-injective b (x ∷ xs) ∙        eq with full x
1+-injective b (x ∷ xs) ∙        eq | yes p = contradiction (proj₂ (∷-injective eq)) (1+-never-∙ xs)
1+-injective b (x ∷ xs) ∙        eq | no ¬p = contradiction (proj₁ (∷-injective eq)) (digit+1-never-0 x ¬p)
1+-injective b (x ∷ xs) (y ∷ ys) eq with full x | full y
1+-injective b (x ∷ xs) (y ∷ ys) eq | yes p | yes q = cong₂ _∷_ x≡y xs≡ys
    where
            x≡y : x ≡ y
            x≡y = Fin-toℕ-injective (trans p (sym q))
            xs≡ys : xs ≡ ys
            xs≡ys = 1+-injective b xs ys (proj₂ (∷-injective eq))
1+-injective b (x ∷ xs) (y ∷ ys) eq | yes p | no ¬q = contradiction (sym (proj₁ (∷-injective eq))) (digit+1-never-0 y ¬q)
1+-injective b (x ∷ xs) (y ∷ ys) eq | no ¬p | yes q = contradiction (proj₁ (∷-injective eq))       (digit+1-never-0 x ¬p)
1+-injective b (x ∷ xs) (y ∷ ys) eq | no ¬p | no ¬q = cong₂ _∷_ (digit+1-injective x y ¬p ¬q (proj₁ (∷-injective eq))) (proj₂ (∷-injective eq))


toℕ-injective : ∀ {b} → (xs ys : Bij (suc b)) → toℕ xs ≡ toℕ ys → xs ≡ ys
toℕ-injective ∙        ∙        eq = refl
toℕ-injective ∙        (y ∷ ys) ()
toℕ-injective (x ∷ xs) ∙        ()
toℕ-injective (x ∷ xs) (y ∷ ys) eq =
    cong₂ _∷_ (proj₁ ind) (toℕ-injective xs ys (proj₂ ind))
    where
            ind : x ≡ y × toℕ xs ≡ toℕ ys
            ind = some-lemma x y (toℕ xs) (toℕ ys) (suc-injective eq)

fromℕ-injective : ∀ b m n → fromℕ {b} m ≡ fromℕ {b} n → m ≡ n
fromℕ-injective b zero    zero    eq = refl
fromℕ-injective b zero    (suc n) eq = contradiction (sym eq) (1+-never-∙ (fromℕ n))
fromℕ-injective b (suc m) zero    eq = contradiction eq       (1+-never-∙ (fromℕ m))
fromℕ-injective b (suc m) (suc n) eq = cong suc (fromℕ-injective b m n (1+-injective b (fromℕ m) (fromℕ n) eq))


--
--      xs ─── 1+ ──➞ 1+ xs
--      |                |
--     toℕ              toℕ
--      ↓                ↓
--      n ─── suc ──➞ suc n
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

fromℕ-toℕ : ∀ {b} xs → fromℕ {b} (toℕ {suc b} xs) ≡ xs
fromℕ-toℕ {b} xs = toℕ-injective (fromℕ (toℕ xs)) xs (toℕ-fromℕ b (toℕ xs))


toℕ-fromℕ-reverse : ∀ b {m} {n} → toℕ (fromℕ {b} m) ≡ n → m ≡ n
toℕ-fromℕ-reverse b {m} {n} eq = begin
        m
    ≡⟨ sym (toℕ-fromℕ b m) ⟩
        toℕ (fromℕ m)
    ≡⟨ eq ⟩
        n
    ∎

fromℕ-toℕ-reverse : ∀ b {xs} {ys} → fromℕ {b} (toℕ {suc b} xs) ≡ ys → xs ≡ ys
fromℕ-toℕ-reverse b {xs} {ys} eq = begin
        xs
    ≡⟨ sym (fromℕ-toℕ xs) ⟩
        fromℕ (toℕ xs)
    ≡⟨ eq ⟩
        ys
    ∎

------------------------------------------------------------------------
-- surjectivity
------------------------------------------------------------------------

toℕ-surjective : ∀ b n → Σ[ xs ∈ Bij (suc b) ] toℕ xs ≡ n
toℕ-surjective b zero    = ∙               , refl
toℕ-surjective b (suc n) = (fromℕ (suc n)) , toℕ-fromℕ b (suc n)


fromℕ-surjective : ∀ {b} (xs : Bij (suc b)) → Σ[ n ∈ ℕ ] fromℕ n ≡ xs
fromℕ-surjective ∙ = zero , refl
fromℕ-surjective (x ∷ xs) = toℕ (x ∷ xs) , fromℕ-toℕ (x ∷ xs)


------------------------------------------------------------------------
-- _⊹_
------------------------------------------------------------------------


toℕ-⊹-homo : ∀ {b} (xs ys : Bij (suc b)) → toℕ (xs ⊹ ys) ≡ toℕ xs + toℕ ys
toℕ-⊹-homo {b} ∙        ys       = refl
toℕ-⊹-homo {b} (x ∷ xs) ∙        = sym (+-right-identity (suc (Fin.toℕ x + toℕ xs * suc b)))
toℕ-⊹-homo {b} (x ∷ xs) (y ∷ ys) with suc (Fin.toℕ x + Fin.toℕ y) divMod (suc b)
toℕ-⊹-homo {b} (x ∷ xs) (y ∷ ys) | result quotient remainder property div-eq mod-eq
    rewrite div-eq | mod-eq
    = begin
            suc (Fin.toℕ remainder + toℕ (n+ quotient (xs ⊹ ys)) * suc b)
        -- apply "toℕ-n+" to remove "n+"
        ≡⟨ cong (λ w → suc (Fin.toℕ remainder + w * suc b)) (toℕ-n+ b quotient (xs ⊹ ys)) ⟩
            suc (Fin.toℕ remainder + (quotient + toℕ (xs ⊹ ys)) * suc b)
        -- the induction hypothesis
        ≡⟨ cong (λ w → suc (Fin.toℕ remainder + (quotient + w) * suc b)) (toℕ-⊹-homo xs ys) ⟩
            suc (Fin.toℕ remainder + (quotient + (toℕ xs + toℕ ys)) * suc b)
        ≡⟨ cong (λ w → suc (Fin.toℕ remainder) + w) (distribʳ-*-+ (suc b) quotient (toℕ xs + toℕ ys)) ⟩
            suc (Fin.toℕ remainder + (quotient * suc b + (toℕ xs + toℕ ys) * suc b))
        ≡⟨ cong suc (sym (+-assoc (Fin.toℕ remainder) (quotient * suc b) ((toℕ xs + toℕ ys) * suc b))) ⟩
            suc (Fin.toℕ remainder + quotient * suc b + (toℕ xs + toℕ ys) * suc b)
        -- apply "property"
        ≡⟨ cong (λ w → suc (w + (toℕ xs + toℕ ys) * suc b)) (sym property) ⟩
            suc (suc (Fin.toℕ x + Fin.toℕ y + (toℕ xs + toℕ ys) * suc b))
        ≡⟨ cong (λ w → suc (suc (Fin.toℕ x + Fin.toℕ y + w))) (distribʳ-*-+ (suc b) (toℕ xs) (toℕ ys)) ⟩
            suc (suc (Fin.toℕ x + Fin.toℕ y + (toℕ xs * suc b + toℕ ys * suc b)))
        ≡⟨ cong (λ w → suc (suc w)) (+-assoc (Fin.toℕ x) (Fin.toℕ y) (toℕ xs * suc b + toℕ ys * suc b)) ⟩
            suc (suc (Fin.toℕ x + (Fin.toℕ y + (toℕ xs * suc b + toℕ ys * suc b))))
        ≡⟨ cong (λ w → suc (suc (Fin.toℕ x + w))) (sym (+-assoc (Fin.toℕ y) (toℕ xs * suc b) (toℕ ys * suc b))) ⟩
            suc (suc (Fin.toℕ x + (Fin.toℕ y + toℕ xs * suc b + toℕ ys * suc b)))
        ≡⟨ cong (λ w → suc (suc (Fin.toℕ x + (w + toℕ ys * suc b)))) (+-comm (Fin.toℕ y) (toℕ xs * suc b)) ⟩
            suc (suc (Fin.toℕ x + (toℕ xs * suc b + Fin.toℕ y + toℕ ys * suc b)))
        ≡⟨ cong (λ w → suc (suc (Fin.toℕ x + w))) (+-assoc (toℕ xs * suc b) (Fin.toℕ y) (toℕ ys * suc b)) ⟩
            suc (suc (Fin.toℕ x + (toℕ xs * suc b + (Fin.toℕ y + toℕ ys * suc b))))
        ≡⟨ cong (λ w → suc (suc w)) (sym (+-assoc (Fin.toℕ x) (toℕ xs * suc b) (Fin.toℕ y + toℕ ys * suc b))) ⟩
            suc (suc ((Fin.toℕ x + toℕ xs * suc b) + (Fin.toℕ y + toℕ ys * suc b)))
        ≡⟨ cong suc (sym (+-suc (Fin.toℕ x + toℕ xs * suc b) (Fin.toℕ y + toℕ ys * suc b))) ⟩
            suc (Fin.toℕ x + toℕ xs * suc b + suc (Fin.toℕ y + toℕ ys * suc b))
        ≡⟨ refl ⟩
            toℕ (x ∷ xs) + toℕ (y ∷ ys)
        ∎

⊹-1+ : ∀ {b} (xs ys : Bij (suc b)) → (1+ xs) ⊹ ys ≡ 1+ (xs ⊹ ys)
⊹-1+ {b} xs ys = toℕ-injective (1+ xs ⊹ ys) (1+ (xs ⊹ ys)) $
    begin
        toℕ (1+ xs ⊹ ys)
    ≡⟨ toℕ-⊹-homo (1+ xs) ys ⟩
        toℕ (1+ xs) + toℕ ys
    ≡⟨ cong (λ w → w + toℕ ys) (toℕ-1+ b xs) ⟩
        suc (toℕ xs + toℕ ys)
    ≡⟨ cong suc (sym (toℕ-⊹-homo xs ys)) ⟩
        suc (toℕ (xs ⊹ ys))
    ≡⟨ sym (toℕ-1+ b (xs ⊹ ys)) ⟩
        toℕ (1+ (xs ⊹ ys))
    ∎

⊹-assoc : ∀ {b} (xs ys zs : Bij (suc b)) → xs ⊹ ys ⊹ zs ≡ xs ⊹ (ys ⊹ zs)
⊹-assoc xs ys zs = toℕ-injective (xs ⊹ ys ⊹ zs) (xs ⊹ (ys ⊹ zs)) $
    begin
        toℕ (xs ⊹ ys ⊹ zs)
    ≡⟨ toℕ-⊹-homo (xs ⊹ ys) zs ⟩
        toℕ (xs ⊹ ys) + toℕ zs
    ≡⟨ cong (λ w → w + toℕ zs) (toℕ-⊹-homo xs ys) ⟩
        toℕ xs + toℕ ys + toℕ zs
    ≡⟨ +-assoc (toℕ xs) (toℕ ys) (toℕ zs) ⟩
        toℕ xs + (toℕ ys + toℕ zs)
    ≡⟨ cong (λ w → toℕ xs + w) (sym (toℕ-⊹-homo ys zs)) ⟩
        toℕ xs + toℕ (ys ⊹ zs)
    ≡⟨ sym (toℕ-⊹-homo xs (ys ⊹ zs)) ⟩
        toℕ (xs ⊹ (ys ⊹ zs))
    ∎

⊹-comm : ∀ {b} (xs ys : Bij (suc b)) → xs ⊹ ys ≡ ys ⊹ xs
⊹-comm xs ys = toℕ-injective (xs ⊹ ys) (ys ⊹ xs) $
    begin
        toℕ (xs ⊹ ys)
    ≡⟨ toℕ-⊹-homo xs ys ⟩
        toℕ xs + toℕ ys
    ≡⟨ +-comm (toℕ xs) (toℕ ys) ⟩
        toℕ ys + toℕ xs
    ≡⟨ sym (toℕ-⊹-homo ys xs) ⟩
        toℕ (ys ⊹ xs)
    ∎



increase-base-lemma : ∀ b
    → (xs : Bij (suc b))
    → toℕ (increase-base xs) ≡ toℕ xs
increase-base-lemma b ∙ = refl
increase-base-lemma b (x ∷ xs) with fromℕ {suc b} (toℕ (increase-base xs) * suc b) | inspect (λ ws → fromℕ {suc b} (toℕ ws * suc b)) (increase-base xs)
increase-base-lemma b (x ∷ xs) | ∙      | [ eq ] = cong suc $
    begin
        Fin.toℕ (Fin.inject₁ x) + 0
    ≡⟨ cong (λ w → w + 0) (FinP.inject₁-lemma x) ⟩
        Fin.toℕ x + 0
    ≡⟨ cong (λ w → Fin.toℕ x + w) $
            begin
                zero
            ≡⟨ cong toℕ (sym eq) ⟩
                toℕ (fromℕ (toℕ (increase-base xs) * suc b))
            ≡⟨ toℕ-fromℕ (suc b) (toℕ (increase-base xs) * suc b) ⟩
                toℕ (increase-base xs) * suc b
            ∎ ⟩
        Fin.toℕ x + toℕ (increase-base xs) * suc b
    ≡⟨ cong (λ w → Fin.toℕ x + w * suc b) (increase-base-lemma b xs) ⟩
        Fin.toℕ x + toℕ xs * suc b
    ∎
increase-base-lemma b (x ∷ xs) | y ∷ ys | [ eq ] with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc (suc b))
increase-base-lemma b (x ∷ xs) | y ∷ ys | [ eq ] | result quotient remainder property div-eq mod-eq
    rewrite div-eq | mod-eq
    = cong suc $ begin
            Fin.toℕ remainder + toℕ (n+ quotient ys) * suc (suc b)
        ≡⟨ cong (λ w → Fin.toℕ remainder + w * suc (suc b)) (toℕ-n+ (suc b) quotient ys) ⟩
            Fin.toℕ remainder + (quotient + toℕ ys) * suc (suc b)
        ≡⟨ cong (λ w → Fin.toℕ remainder + w) (distribʳ-*-+ (suc (suc b)) quotient (toℕ ys)) ⟩
            Fin.toℕ remainder + (quotient * suc (suc b) + toℕ ys * suc (suc b))
        ≡⟨ sym (+-assoc (Fin.toℕ remainder) (quotient * suc (suc b)) (toℕ ys * suc (suc b))) ⟩
            Fin.toℕ remainder + quotient * suc (suc b) + toℕ ys * suc (suc b)
        ≡⟨ cong (λ w → w + toℕ ys * suc (suc b)) (sym property) ⟩
            suc (Fin.toℕ x + Fin.toℕ y + toℕ ys * suc (suc b))
        ≡⟨ cong suc (+-assoc (Fin.toℕ x) (Fin.toℕ y) (toℕ ys * suc (suc b))) ⟩
            suc (Fin.toℕ x + (Fin.toℕ y + toℕ ys * suc (suc b)))
        ≡⟨ sym (+-suc (Fin.toℕ x) (Fin.toℕ y + toℕ ys * suc (suc b))) ⟩
            Fin.toℕ x + suc (Fin.toℕ y + toℕ ys * suc (suc b))
        ≡⟨ cong (λ w → Fin.toℕ x + toℕ w) (sym eq) ⟩
            Fin.toℕ x + toℕ (fromℕ (toℕ (increase-base xs) * suc b))
        ≡⟨ cong (λ w → Fin.toℕ x + w) (toℕ-fromℕ (suc b) (toℕ (increase-base xs) * suc b)) ⟩
            Fin.toℕ x + toℕ (increase-base xs) * suc b
        ≡⟨ cong (λ w → Fin.toℕ x + w * suc b) (increase-base-lemma b xs) ⟩
            Fin.toℕ x + toℕ xs * suc b
        ∎

decrease-base-lemma : ∀ b → (xs : Bij (suc (suc b))) → toℕ (decrease-base xs) ≡ toℕ xs
decrease-base-lemma b ∙ = refl
decrease-base-lemma b (x ∷ xs) with fromℕ {b} (toℕ (decrease-base xs) * suc (suc b))
              | inspect (λ ws → fromℕ {b} (toℕ ws * suc (suc b))) (decrease-base xs)
decrease-base-lemma b (x ∷ xs) | ∙ | [ eq ] with full x
decrease-base-lemma b (x ∷ xs) | ∙ | [ eq ] | yes p = cong suc $
    begin
        suc (b + 0)
    ≡⟨ cong (λ w → w + 0) (sym p)⟩
        Fin.toℕ x + zero
    ≡⟨ cong (λ w → Fin.toℕ x + w) $
            begin
                zero
            ≡⟨ cong toℕ (sym eq) ⟩
                toℕ (fromℕ (toℕ (decrease-base xs) * suc (suc b)))
            ≡⟨ toℕ-fromℕ b (toℕ (decrease-base xs) * suc (suc b)) ⟩
                toℕ (decrease-base xs) * suc (suc b)
            ∎ ⟩
        Fin.toℕ x + toℕ (decrease-base xs) * suc (suc b)
    ≡⟨ cong (λ w → Fin.toℕ x + w * suc (suc b)) (decrease-base-lemma b xs) ⟩
        Fin.toℕ x + toℕ xs * suc (suc b)
    ∎
decrease-base-lemma b (x ∷ xs) | ∙ | [ eq ] | no ¬p = cong suc $
    begin
        Fin.toℕ (inject-1 x ¬p) + 0
    ≡⟨ cong (λ w → w + 0) (inject-1-lemma x ¬p) ⟩
        Fin.toℕ x + 0
    ≡⟨ cong (λ w → Fin.toℕ x + w) $
            begin
                zero
            ≡⟨ cong toℕ (sym eq) ⟩
                toℕ (fromℕ (toℕ (decrease-base xs) * suc (suc b)))
            ≡⟨ toℕ-fromℕ b (toℕ (decrease-base xs) * suc (suc b)) ⟩
                toℕ (decrease-base xs) * suc (suc b)
            ∎ ⟩
        Fin.toℕ x + toℕ (decrease-base xs) * suc (suc b)
    ≡⟨ cong (λ w → Fin.toℕ x + w * suc (suc b)) (decrease-base-lemma b xs) ⟩
        Fin.toℕ x + toℕ xs * suc (suc b)
    ∎
decrease-base-lemma b (x ∷ xs) | y ∷ ys | [ eq ] with (suc (Fin.toℕ x + Fin.toℕ y)) divMod (suc b)
decrease-base-lemma b (x ∷ xs) | y ∷ ys | [ eq ] | result quotient remainder property div-eq mod-eq
    rewrite div-eq | mod-eq = cong suc $ begin
            Fin.toℕ remainder + toℕ (n+ quotient ys) * suc b
        ≡⟨ cong (λ w → Fin.toℕ remainder + w * suc b) (toℕ-n+ b quotient ys) ⟩
            Fin.toℕ remainder + (quotient + toℕ ys) * suc b
        ≡⟨ cong (λ w → Fin.toℕ remainder + w) (distribʳ-*-+ (suc b) quotient (toℕ ys)) ⟩
            Fin.toℕ remainder + (quotient * suc b + toℕ ys * suc b)
        ≡⟨ sym (+-assoc (Fin.toℕ remainder) (quotient * suc b) (toℕ ys * suc b)) ⟩
            Fin.toℕ remainder + quotient * suc b + toℕ ys * suc b
        ≡⟨ cong (λ w → w + toℕ ys * suc b) (sym property) ⟩
            suc (Fin.toℕ x + Fin.toℕ y + toℕ ys * suc b)
        ≡⟨ cong suc (+-assoc (Fin.toℕ x) (Fin.toℕ y) (toℕ ys * suc b)) ⟩
            suc (Fin.toℕ x + (Fin.toℕ y + toℕ ys * suc b))
        ≡⟨ sym (+-suc (Fin.toℕ x) (Fin.toℕ y + toℕ ys * suc b)) ⟩
            Fin.toℕ x + suc (Fin.toℕ y + toℕ ys * suc b)
        ≡⟨ cong (λ w → Fin.toℕ x + toℕ w) (sym eq) ⟩
            Fin.toℕ x + toℕ (fromℕ (toℕ (decrease-base xs) * suc (suc b)))
        ≡⟨ cong (λ w → Fin.toℕ x + w) (toℕ-fromℕ b (toℕ (decrease-base xs) * suc (suc b))) ⟩
            Fin.toℕ x + toℕ (decrease-base xs) * suc (suc b)
        ≡⟨ cong (λ w → Fin.toℕ x + w * suc (suc b)) (decrease-base-lemma b xs) ⟩
            Fin.toℕ x + toℕ xs * suc (suc b)
        ∎

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
