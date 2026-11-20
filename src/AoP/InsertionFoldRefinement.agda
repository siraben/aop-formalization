{-# OPTIONS --safe --without-K #-}
module AoP.InsertionFoldRefinement where

open import AoP.Prelude
open import AoP.InsertionSort using (insert; sort)
open import AoP.OrderedInsertionFold using (Fold; base; step)
open import AoP.SetSort using () renaming (insert to occurrence)
open import AoP.SelectionSort using (Sorted)
open import Agda.Builtin.Nat using (Nat)

-- Last refinement of exercise 6.30. At each step the deterministic
-- insert chooses a legal occurrence in the guarded relational fold.
-- Follow the actual recursive calls so the witness describes the
-- program's choices, including which equal key was inserted.
refines : ∀ xs → Fold xs (fst (sort xs))
refines [] = base
refines (a ∷ xs) with sort xs | refines xs
... | ys , perm , ok | history with insert a ys ok
...   | zs , removed , sorted = step history (occurrence removed) sorted
