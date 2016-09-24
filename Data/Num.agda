module Data.Num where

open import Data.Num.Core public
open import Data.Num.Surjection public hiding (1+)
open import Data.Num.Injection public
open import Data.Num.Bijection public

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties.Extra
open import Data.Nat.DM
open import Data.Fin.Properties using (bounded)
open import Data.Fin as Fin
    using (Fin; fromℕ≤; inject≤; #_)
    renaming (zero to z; suc to s)
-- open import Data.Fin.Properties as FinProps using ()
open import Data.Product
    using (Σ-syntax; Σ; _,_)
open import Function
open import Function.Surjection
open import Function.Injection
open import Function.Bijection

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≈⟨_⟩_)

open DecTotalOrder decTotalOrder using (reflexive) renaming (refl to ≤-refl)


_⊹_ : ∀ {b d o}
    → {surj : True (Surjective? b d o)}
    → (xs ys : Num b d o)
    → Num b d o
_⊹_ {b} {d} {o}      xs       ys        with Surjective? b d o
_⊹_ {b} {d} {o}      ∙        ∙        | yes surj = ∙
_⊹_ {b} {d} {o}      ∙        (y ∷ ys) | yes surj = y ∷ ys
_⊹_ {b} {d} {o}      (x ∷ xs) ∙        | yes surj = x ∷ xs
_⊹_ {b} {d} {o}      (x ∷ xs) (y ∷ ys) | yes surj with _divMod_ (o + Fin.toℕ x + Fin.toℕ y) b {fromWitnessFalse (>⇒≢ (Surjective⇒b≥1 surj))}
_⊹_ {b} {d} {o}      (x ∷ xs) (y ∷ ys) | yes surj | result quotient remainder property div-eq mod-eq =
    inject≤ remainder d≥b ∷ n+ quotient (_⊹_ {surj = fromWitness surj} xs ys)
    where   d≥b : d ≥ b
            d≥b = Surjective⇒d≥b surj
_⊹_ {b} {d} {o} {()} xs ys | no ¬surj


-- (incrementable n) if there exists some n' : Num b d o such that ⟦ n' ⟧ℕ ≡ suc ⟦ n ⟧ℕ
incrementable : ∀ {b d o} → Num b d o → Set
incrementable {b} {d} {o} xs = Σ[ xs' ∈ Num b d o ] toℕ xs' ≡ suc (toℕ xs)

-- when a system has no digits at all
incrementable-lemma-no-digits : ∀ {b o} → (xs : Num b 0 o) → ¬ (incrementable xs)
incrementable-lemma-no-digits ∙ (∙ , ())
incrementable-lemma-no-digits ∙ (() ∷ xs , p)
incrementable-lemma-no-digits (() ∷ xs)

Num-b-1-0⇒≡0 : ∀ {b} → (xs : Num b 1 0) → toℕ xs ≡ 0
Num-b-1-0⇒≡0     ∙           = refl
Num-b-1-0⇒≡0 {b} (z    ∷ xs) = cong (λ w → w * b) (Num-b-1-0⇒≡0 xs)
Num-b-1-0⇒≡0     (s () ∷ xs)

Num-0-d-o⇒<d+o : ∀ {d o} → (xs : Num 0 (suc d) o) → toℕ xs < suc d + o
Num-0-d-o⇒<d+o ∙ = s≤s z≤n
Num-0-d-o⇒<d+o {d} {o} (x ∷ xs) = s≤s $
    start
        Digit-toℕ x o + toℕ xs * zero
    ≤⟨ reflexive $ begin
            Digit-toℕ x o + toℕ xs * zero
        ≡⟨ cong (_+_ (Digit-toℕ x o)) (*-right-zero (toℕ xs)) ⟩
            Digit-toℕ x o + zero
        ≡⟨ +-right-identity (Digit-toℕ x o) ⟩
            Digit-toℕ x o
    ∎ ⟩
        Digit-toℕ x o
    ≤⟨ ≤-pred (Digit<d+o x o) ⟩
        d + o
    □

-- when a system has only the digit 0
Num-b-1-0⇒¬incrementable : ∀ {b} → (xs : Num b 1 0) → ¬ (incrementable xs)
Num-b-1-0⇒¬incrementable {b} xs (xs' , p) = contradiction (
    begin
        0
    ≡⟨ sym (Num-b-1-0⇒≡0 xs') ⟩
        toℕ xs'
    ≡⟨ p ⟩
        suc (toℕ xs)
    ≡⟨ cong suc (Num-b-1-0⇒≡0 xs) ⟩
        1
    ∎) (λ ())

¬incrementable-lemma-2 : ∀ {b d o} → ¬ (incrementable {b} {suc d} {suc (suc o)} ∙)
¬incrementable-lemma-2 (∙ , ())
¬incrementable-lemma-2 (x ∷ xs , ())


¬incrementable-lemma-3 : ∀ {d o} → (x : Digit (suc d)) → (xs : Num 0 (suc d) o) → ¬ (incrementable (x ∷ xs))
¬incrementable-lemma-3 x ∙ (xs' , p) = {!   !}
¬incrementable-lemma-3 x (x₁ ∷ xs) (xs' , p) = {!   !}
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

mutual
    incrementable? : ∀ {b d o} → (xs : Num b d o) → Dec (incrementable xs)
    incrementable? {_} {zero}               xs = no (incrementable-lemma-no-digits xs)
    incrementable? {_} {suc zero}    {zero} ∙  = no (Num-b-1-0⇒¬incrementable ∙)
    incrementable? {_} {suc (suc d)} {zero} ∙  = yes ((fromℕ≤ {1} (s≤s (s≤s z≤n)) ∷ ∙) , refl)
    incrementable? {d = suc d} {suc zero} ∙ = yes (z ∷ ∙ , refl)
    incrementable? {d = suc d} {suc (suc o)} ∙ = no ¬incrementable-lemma-2
    incrementable? {d = suc d} (x ∷ xs) with full x
    incrementable? {b} {suc d} (x ∷ xs) | yes p with incrementable? xs
    incrementable? {b} {suc d} (x ∷ xs) | yes p | yes q with b ≤? d
    incrementable? {zero} {suc d} (x ∷ xs) | yes p | yes q | yes r =
        no {!   !}
    incrementable? {suc b} {suc d} (x ∷ xs) | yes p | yes q | yes r
        = yes ((digit+1-b {suc b} {suc d} x (s≤s z≤n) p ∷ 1+ xs (fromWitness q)) , {!   !})
    -- incrementable? {b} {suc d} (x ∷ xs) | yes p | yes q | yes r = yes ({! digit+1-b {b} {suc d} x   !} , {!   !})
    incrementable? {b} {suc d} (x ∷ xs) | yes p | yes q | no ¬r = no {!   !}
    incrementable? {b} {suc d} (x ∷ xs) | yes p | no ¬q = no {!   !}
    incrementable? {b} {suc d} (x ∷ xs) | no ¬p = yes {!   !}

    1+ : ∀ {b d o} → (xs : Num b d o) → True (incrementable? xs) → Num b d o
    1+ {d = zero} xs ()
    1+ {d = suc zero} {zero} ∙ ()
    1+ {d = suc (suc d)} {zero} ∙ p = fromℕ≤ {1} (s≤s (s≤s z≤n)) ∷ ∙
    1+ {d = suc d} {suc zero} ∙ p = z ∷ ∙
    1+ {d = suc d} {suc (suc o)} ∙ p = contradiction (toWitness p) ((¬incrementable-lemma-2 {_} {d} {o}))
    1+ {d = suc d} (x ∷ xs) p with full x
    1+ {b} {suc d} (x ∷ xs) p₁ | yes p with incrementable? xs
    1+ {b} {suc d} (x ∷ xs) p₂ | yes p | yes q with b ≤? d
    1+ {b} {suc d} (x ∷ xs) p₂ | yes p | yes q | yes r = {!   !}
    1+ {b} {suc d} (x ∷ xs) p₂ | yes p | yes q | no ¬r = {!   !}
    1+ {b} {suc d} (x ∷ xs) p₁ | yes p | no ¬q = {!   !}
    1+ {b} {suc d} (x ∷ xs) p | no ¬p = {!   !}

-- -- no digits
-- incrementable? {b} {zero} {o} ∙ = no (incrementable-lemma-no-digits ∙)
-- -- the system only the digit 0
-- incrementable? {b} {suc zero} {zero} ∙ = no (Num-b-1-0⇒¬incrementable ∙)
-- -- the system has 2 digits {0, 1}
-- incrementable? {b} {suc (suc d)} {zero} ∙ = yes ((fromℕ≤ {1} (s≤s (s≤s z≤n)) ∷ ∙) , refl)
-- incrementable? {b} {suc d} {suc zero} ∙ = yes (z ∷ ∙ , refl)
-- -- offset = 2, it's impossible for "1" to exist
-- incrementable? {b} {suc d} {suc (suc o)} ∙ = no ¬incrementable-lemma-2
-- incrementable? {b} {d} {o} (x ∷ xs) with full x
-- -- x is at its largest, needs to carry in order to be incrementable
-- incrementable? (x ∷ xs) | yes p with incrementable? xs
-- incrementable? (x ∷ xs) | yes p | yes q = yes ((fromℕ≤ {0} {!   !} ∷ {!   !}) , {!   !})
-- incrementable? (x ∷ xs) | yes p | no ¬q = {!   !}
-- incrementable? (x ∷ xs) | no ¬p = yes ((digit+1 x ¬p ∷ xs) , {!   !})

-- incrementable? : ∀ {b d o} → (xs : Num b d o) → Dec (incrementable xs)
-- incrementable? ∙ = {!   !}
-- incrementable? (x ∷ xs) = {!   !}
-- incrementable? : ∀ {b d o}
--     → (xs : Num b d o)
--     →
--     → Σ[ xs' ∈ Num b d o ] toℕ xs' ≡ suc (toℕ xs)
-- incrementable? ∙ = {!   !} , {!   !}
-- incrementable? (x ∷ xs) = {!   !}



normalize : ∀ {b d o} → Num b d o → Num b d o
normalize {b} {d} {o} ∙ = ∙
normalize {b} {d} {o} (x ∷ xs) with Injective? b d o
-- injective systems are not redundant, normalization has no effects on these numbers
normalize {b} {d} {o} (x ∷ xs) | yes inj = x ∷ xs
normalize {b} {d} {o} (x ∷ xs) | no ¬inj with Surjective? b d o
normalize {b} {d} {o} (x ∷ xs) | no ¬inj | yes surj with _divMod_ (Digit-toℕ x o) b {fromWitnessFalse (>⇒≢ (Surjective⇒b≥1 surj))}
normalize {b} {d} {o} (x ∷ xs) | no ¬inj | yes surj | result quotient remainder property div-eq mod-eq
    = LSD ∷ n+ quotient xs
    where   d≥b : d ≥ b
            d≥b = Surjective⇒d≥b surj
            LSD : Digit d
            LSD = inject≤ remainder d≥b
normalize (x ∷ ∙) | no ¬inj | no ¬surj = {!   !}
normalize (x ∷ y ∷ xs) | no ¬inj | no ¬surj = {!   !}

-- normalize : ∀ {b d o} → Num b d o → Num b d o
-- normalize {b} {d} {o} ∙ = ∙
-- normalize {b} {d} {o} (x ∷ xs) with injectionView b d o
-- -- injective systems are not redundant, normalization has no effects on these numbers
-- normalize {b} {d} {o} (x ∷ xs) | Inj _ = xs
--
-- normalize {b} {d} {o} (x ∷ xs) | NonInj _ with surjectionView b d o
-- normalize {b} {d} {o} (x ∷ xs) | NonInj _ | Surj surjCond with (Digit-toℕ x o) divMod b
-- normalize {b} {d} {o} (x ∷ xs) | NonInj _ | Surj surjCond | result quotient remainder property div-eq mod-eq
--     = {!   !} ∷ {!   !}
--     where   d≥b : d ≥ b
--             d≥b = Surjective⇒d≥b surj
-- normalize {b} {d} {o} (x ∷ xs) | NonInj _ | NonSurj _ = {!   !}

_≋_ : ∀ {b d o}
    → (xs ys : Num b d o)
    → Set
_≋_ {b}     {d}     {o} ∙        ∙        = ⊤

_≋_ {b}     {d}     {o} ∙        (y ∷ ys) with Digit-toℕ y o ≟ 0
_≋_ {zero}  {d}     {o} ∙        (y ∷ ys) | yes p = ⊤
_≋_ {suc b} {d}         ∙        (y ∷ ys) | yes p = ∙ ≋ ys
_≋_ {b}     {d}         ∙        (y ∷ ys) | no ¬p = ⊥

_≋_ {b}     {d}     {o} (x ∷ xs) ∙        with Digit-toℕ x o ≟ 0
_≋_ {zero}              (x ∷ xs) ∙        | yes p = ⊤
_≋_ {suc b}             (x ∷ xs) ∙        | yes p = xs ≋ ∙
_≋_ {b}     {d}     {o} (x ∷ xs) ∙        | no ¬p = ⊥
-- things get trickier here, we cannot say two numbers are equal or not base on
-- their LSD, since the system may be redundant.
_≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) with Digit-toℕ x o ≟ Digit-toℕ y o
_≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) | yes p = xs ≋ ys
_≋_ {b}     {d}     {o} (x ∷ xs) (y ∷ ys) | no ¬p = ⊥

-- indexing bijective systems
BijN : ℕ → Set
BijN b = Num (suc b) (suc b) 1

BijN⇒Surjective : ∀ b → Surjective (Num⟶ℕ (suc b) (suc b) 1)
BijN⇒Surjective b with surjectionView (suc b) (suc b) 1
BijN⇒Surjective b | Surj surjCond = SurjCond⇒Surjective surjCond
BijN⇒Surjective b | NonSurj (Offset≥2 (s≤s ()))
BijN⇒Surjective b | NonSurj (NotEnoughDigits _ d≱b) = contradiction (s≤s ≤-refl) d≱b

BijN⇒Injective : ∀ b → Injective (Num⟶ℕ (suc b) (suc b) 1)
BijN⇒Injective b with injectionView (suc b) (suc b) 1
BijN⇒Injective b | Inj injCond = InjCond⇒Injective injCond
BijN⇒Injective b | NonInj (Redundant d>b) = contradiction refl (>⇒≢ d>b)

BijN⇒Bijective : ∀ b → Bijective (Num⟶ℕ (suc b) (suc b) 1)
BijN⇒Bijective b with bijectionView (suc b) (suc b) 1
BijN⇒Bijective b | Bij surjCond injCond = SurjCond∧InjCond⇒Bijective surjCond injCond
BijN⇒Bijective b | NonSurj (Offset≥2 (s≤s ()))
BijN⇒Bijective b | NonSurj (NotEnoughDigits _ d≱b) = contradiction (s≤s ≤-refl) d≱b
BijN⇒Bijective b | NonInj (Redundant d>b) = contradiction refl (>⇒≢ d>b)
