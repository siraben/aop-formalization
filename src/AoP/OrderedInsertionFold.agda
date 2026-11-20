{-# OPTIONS --safe --without-K #-}
module AoP.OrderedInsertionFold where

open import AoP.Prelude
open import AoP.Permutations using (Perm; empty; insert; Insert; front; later)
open import AoP.Selection using (Remove; head; past)
open import AoP.SelectionSort using (Sorted; nil; cons)
open import AoP.InsertionSort using (ordered-delete)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 6.30. The relational fold chooses an insertion at each
-- cons, guarding its output immediately. Fusing the final order test
-- into the fold preserves exactly the accepted input/output pairs.
data Fold : List Nat → List Nat → Set where
  base : Fold [] []
  step : ∀ {a xs ys zs} → Fold xs ys → Insert a ys zs → Sorted zs → Fold (a ∷ xs) zs

private
  remove : ∀ {a : Nat} {ys zs} → Insert a ys zs → Remove a zs ys
  remove front = head
  remove (later i) = past (remove i)

fuse : ∀ {xs ys} → Perm xs ys → Sorted ys → Fold xs ys
fuse empty nil = base
fuse (insert p i) ord = step (fuse p (ordered-delete (remove i) ord)) i ord
unfuse : ∀ {xs ys} → Fold xs ys → Perm xs ys × Sorted ys
unfuse base = empty , nil
unfuse (step rec i ord) = insert (fst (unfuse rec)) i , ord
