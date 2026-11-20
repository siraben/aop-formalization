{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.MergeTreeSort where

open import AoP.Common.Prelude
open import AoP.Chapter06.PreorderSort using (Tree; null; fork)
open import AoP.Chapter06.Selection
open import AoP.Chapter06.SelectionSort using (length; shorter; remaining; Perm; Sorted; Result; finish; emit; nil; cons; perm-bound; remove-bound)
open import AoP.Chapter06.InsertionSort using (carry)
open import AoP.Chapter06.OrderedMerge as M using (Merge; merge; exhaustedˡ; exhaustedʳ; left; right)
open import AoP.Common.NatOrder using (_≤_; s≤; rid) renaming (weaken to increase)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 6.28. Emit the root and merge the two child traversals. Build
-- a minimum-rooted tree: after selecting a minimum, give one remaining
-- key to the left child and recursively build the right child from the
-- rest. Unlike preorder traversal, the two sides may interleave.
flatten : Tree → List Nat
flatten null = []
flatten (fork l a r) = a ∷ fst (merge (flatten l) (flatten r))

-- A merge with a singleton inserts exactly one occurrence into the
-- other child's output. This lifts its permutation to the entire tail.
single : ∀ {x ys zs} → Merge (x ∷ []) ys zs → Remove x zs ys
single (exhaustedʳ _) = head
single (left _ (exhaustedˡ _)) = head
single (right _ m) = past (single m)

record Build (xs : List Nat) : Set where
  constructor built
  field
    tree : Tree
    perm : Perm xs (flatten tree)
    sorted : Sorted (flatten tree)

build : ∀ n xs → length xs ≤ n → Build xs
build n [] _ = built null finish nil
build (suc n) (x ∷ xs) (s≤ fuel) with select x xs
... | chose a [] removal lb = built (fork null a null) (emit removal finish) (cons empty nil)
... | chose a (k ∷ ks) removal lb with remaining (shorter removal) fuel | snd (remove-bound removal lb)
...   | s≤ smaller | below ak lower with build n ks (increase smaller)
...     | built r perm sorted = built (fork (fork null k null) a r) (emit removal tail-perm)
                                (cons (M.bound m (below ak empty) (perm-bound perm lower))
                                      (M.ordered m (cons empty nil) sorted))
  where
  m = snd (merge (k ∷ []) (flatten r))
  tail-perm = carry (single m) perm

sort : ∀ xs → Result xs
sort xs with build (length xs) xs (rid _)
... | built t perm sorted = flatten t , perm , sorted

example : fst (sort (4 ∷ 1 ∷ 2 ∷ 3 ∷ [])) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
example = refl
