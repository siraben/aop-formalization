{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.PreorderSort where

open import AoP.Common.Prelude
open import AoP.Chapter06.Selection
open import AoP.Chapter06.SelectionSort using (length; shorter; remaining; Sorted; nil; cons; Perm; finish; emit; Result; perm-bound; remove-bound)
open import AoP.Common.NatOrder using (_≤_; s≤; rid)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 6.26. In preorder, the root appears before both children.
-- Consequently the root of an ordered traversal must be a minimum.
-- Choose a least occurrence, leave the left child empty, and place all
-- remaining keys in the right child. This gives a selection procedure
-- through the exercise's binary tree and its preorder join.
data Tree : Set where
  null : Tree
  fork : Tree → Nat → Tree → Tree

preorder : Tree → List Nat
preorder null = []
preorder (fork l a r) = a ∷ (preorder l ++ preorder r)

record Build (xs : List Nat) : Set where
  constructor built
  field
    tree : Tree
    rearranges : Perm xs (preorder tree)
    ordered : Sorted (preorder tree)

build : ∀ n xs → length xs ≤ n → Build xs
build n [] _ = built null finish nil
build (suc n) (x ∷ xs) (s≤ fuel) with select x xs
... | chose a rest removed lb with build n rest (remaining (shorter removed) fuel)
...   | built t perm ok = built (fork null a t) (emit removed perm)
                          (cons (perm-bound perm (snd (remove-bound removed lb))) ok)

sort : ∀ xs → Result xs
sort xs with build (length xs) xs (rid _)
... | built t perm ok = preorder t , perm , ok

example : fst (sort (3 ∷ 1 ∷ 2 ∷ [])) ≡ 1 ∷ 2 ∷ 3 ∷ []
example = refl
