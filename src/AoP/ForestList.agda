{-# OPTIONS --safe --without-K #-}
module AoP.ForestList where

open import AoP.Prelude
open import AoP.Trees
open import AoP.Folds using (⦅_∣_⦆)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Nat using (Nat; zero; suc)
private variable A B C : Set

-- §1.4. Changing the tip labels leaves the shape unchanged.
numbers : Tree Nat
numbers = bin (tip 0) (bin (tip 1) (tip 2))
letters : Tree Char
letters = bin (tip 'A') (bin (tip 'B') (tip 'C'))

label : Nat → Char
label zero = 'A'
label (suc zero) = 'B'
label (suc (suc _)) = 'C'

relabelling : map label numbers ≡ letters
relabelling = refl
shape : (size letters ≡ 3) × (depth letters ≡ 2)
shape = refl , refl

-- A forest is an ordered list of rose trees. Both conversions leave
-- the trees intact; only the spine constructors change.
toList : Forest A → List (Rose A)
toList null = []
toList (grow t ts) = t ∷ toList ts

fromList : List (Rose A) → Forest A
fromList = ⦅ null ∣ grow ⦆

list-law : (ts : List (Rose A)) → toList (fromList ts) ≡ ts
list-law [] = refl
list-law (t ∷ ts) = cong (t ∷_) (list-law ts)

forest-law : (ts : Forest A) → fromList (toList ts) ≡ ts
forest-law null = refl
forest-law (grow t ts) = cong (grow t) (forest-law ts)

-- The forest half of the mutual fold is an ordinary list fold in
-- these coordinates. Each tree is reduced before combining siblings.
module Transport (node : A → C → B) (e : C) (join : B → C → C) where
  open RoseFold node e join
  law : ∀ ts → forest ts ≡ ⦅ e ∣ (λ t → join (tree t)) ⦆ (toList ts)
  law null = refl
  law (grow t ts) = cong (join (tree t)) (law ts)
