{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.QuickSplitWork where

open import AoP.Common.Prelude
open import AoP.Chapter06.Quicksort
open import AoP.Chapter06.SelectionSort using (length)
open import AoP.Common.NatOrder using (rid)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Count pivot comparisons only. Each left/right trace constructor
-- corresponds to one call to compare, and choosing the pivot uses none.
pass : ∀ {p xs l r} → Split p xs l r → Nat
pass (pivot _) = 0
pass (left _ s) = suc (pass s)
pass (right _ s) = suc (pass s)
pass-size : ∀ {p xs l r} (s : Split p xs l r) → suc (pass s) ≡ length xs
pass-size (pivot _) = refl
pass-size (left _ s) = cong suc (pass-size s)
pass-size (right _ s) = cong suc (pass-size s)

work : ∀ {xs} → Tree xs → Nat
work null = 0
work (fork _ s l r) = pass s + (work l + work r)

-- Track every intermediate pivot and both children on the duplicate
-- example. Leaves marked empty correspond to empty recursive inputs.
data View : Set where
  empty : View
  node : Nat → View → View → View
view : ∀ {xs} → Tree xs → View
view null = empty
view (fork p _ l r) = node p (view l) (view r)
input = 3 ∷ 1 ∷ 2 ∷ 2 ∷ []
tree = unfold (length input) input (rid _)
shape : view tree ≡ node 2 (node 2 (node 1 empty empty) empty) (node 3 empty empty)
shape = refl
comparisons : work tree ≡ 4
comparisons = refl
