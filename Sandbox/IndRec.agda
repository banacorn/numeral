module Sandbox.IndRec where
-- Ornamental Algebras, Algebraic Ornaments, CONOR McBRIDE
-- https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf
-- A Finite Axiomtization of Inductive-Recursion definitions, Peter Dybjer, Anton Setzer
-- http://www.cse.chalmers.se/~peterd/papers/Finite_IR.pdf

open import Data.Product using (_×_; Σ; _,_)
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data Desc : Set₁ where
    arg : (A : Set)             -- a bag of tags to choose constructors with
        → (A → Desc)            -- given a tag, return the description of the constructor it corresponds to
        → Desc
    rec : Desc → Desc           -- recursive subnode
    ret : Desc                  -- stop

-- the "decoder", "interpreter"
⟦_⟧ : Desc → Set → Set
⟦ arg A D ⟧ R = Σ A (λ a → ⟦ D a ⟧ R)
⟦ rec D   ⟧ R = R × ⟦ D ⟧ R
⟦ ret     ⟧ R = ⊤

-- "μ" in some other literature
data Data (D : Desc) : Set where
    ⟨_⟩ : ⟦ D ⟧ (Data D) → Data D   -- or "in"

out : ∀ {D} → Data D → ⟦ D ⟧ (Data D)
out ⟨ x ⟩ = x

map : ∀ {A B} → (d : Desc) → (A → B) → ⟦ d ⟧ A → ⟦ d ⟧ B
map (arg A  d) f (a , y) = a , (map (d a) f y)
map (rec desc) f (a , x) = (f a) , (map desc f x)
map (ret) f tt = tt

-- fold : ∀ {A} → (F : Desc) → (⟦ F ⟧ A → A) → Data F → A
-- fold F alg ⟨ x ⟩ = alg (map F (fold F alg) x)

-- mapFold F alg x = map F (fold F alg) x
-- fold F alg x = alg (mapFold F alg (out x))
-- mapFold F alg x = map F (λ y → alg (mapFold F alg (out y))) x


mapFold : ∀ {A} (F G : Desc) → (⟦ G ⟧ A → A) → ⟦ F ⟧ (Data G) → ⟦ F ⟧ A
mapFold (arg T decoder) G alg (t , cnstrctr) = t , (mapFold (decoder t) G alg cnstrctr)
mapFold (rec F) G alg (⟨ x ⟩ , xs) = alg (mapFold G G alg x) , mapFold F G alg xs
mapFold ret G alg x = tt

fold : ∀ {A} → (F : Desc) → (⟦ F ⟧ A → A) → Data F → A
fold F alg ⟨ x ⟩ = alg (mapFold F F alg x)

-- ℕ
ℕDesc : Desc
ℕDesc = arg Bool λ { false → ret ; true → rec ret }

ℕ : Set
ℕ = Data ℕDesc

zero : ℕ
zero = ⟨ (false , tt) ⟩

suc : ℕ → ℕ
suc n = ⟨ (true , (n , tt)) ⟩

-- induction principle on ℕ
indℕ : (P : ℕ → Set)
     → (P zero)
     → ((n : ℕ) → (P n) → (P (suc n)))
     → (x : ℕ)
     → P x
indℕ P base step ⟨ true , n-1 , _ ⟩ = step n-1 (indℕ P base step n-1)
indℕ P base step ⟨ false , _ ⟩ = base

_+_ : ℕ → ℕ → ℕ
x + y = indℕ (λ _ → ℕ) y (λ n x → suc x) x

-- Maybe
MaybeDesc : Set → Desc
MaybeDesc A = arg Bool (λ { false → ret ; true → arg A (λ x → ret) })

Maybe : Set → Set
Maybe A = Data (MaybeDesc A)

nothing : ∀ {A} → Maybe A
nothing = ⟨ (false , tt) ⟩

just : ∀ {A} → A → Maybe A
just a = ⟨ (true , (a , tt)) ⟩

mapMaybe : ∀ {A B} → (A → B) → Maybe A → Maybe B
mapMaybe f ⟨ true , a , tt ⟩ = ⟨ (true , ((f a) , tt)) ⟩
mapMaybe f ⟨ false , tt ⟩ = ⟨ false , tt ⟩

-- List
ListDesc : Set → Desc
ListDesc A = arg Bool (λ { false → ret ; true → arg A (λ _ → rec ret )})

List : Set → Set
List A = Data (ListDesc A)

nil : ∀ {A} → List A
nil = ⟨ (false , tt) ⟩

cons : ∀ {A} → A → List A → List A
cons x xs = ⟨ (true , (x , (xs , tt))) ⟩

-- mapList : ∀ {A B} → (A → B) → List A → List B
-- mapList f ⟨ true , x , xs , tt ⟩ = ⟨ (true , ((f x) , ((mapList f xs) , tt))) ⟩
-- mapList f ⟨ false , tt ⟩ = ⟨ false , tt ⟩

-- indList : ∀ {A} (P : List A → Set)
--         → P nil
--         → ((x : A) → (xs : List A) → P xs → P (cons x xs))
--         → (xs : List A)
--         → P xs
-- indList {A} P base step xs = fold (ListDesc A) f xs
--     where   f : ⟦ ListDesc A ⟧ (P xs) → P xs
--             f (true , x , Pxs , tt) = {!   !}
--             f (false , tt) = {!   !}

foldList : ∀ {A B} (f : A → B → B) → B → List A → B
foldList {A} {B} f e xs = fold (ListDesc A) alg xs
    where   alg : ⟦ ListDesc A ⟧ B → B
            alg (true , n , acc , tt) = f n acc
            alg (false , tt) = e
