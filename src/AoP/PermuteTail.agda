{-# OPTIONS --safe --without-K #-}
module AoP.PermuteTail where

open import AoP.Prelude
open import AoP.Permutations using (Perm; empty; insert; front)
open import AoP.QuickPermutation using (compose)
private variable A : Set

-- Exercise 5.28, in the insertion presentation of bag equality. A
-- preliminary permutation of the tail changes no possible final output.
-- Keep the head at the front to lift the tail permutation, then compose
-- with the final permutation. In the other direction choose the original
-- tail itself as the intermediate list.
identity : (xs : List A) → Perm xs xs
identity [] = empty
identity (_ ∷ xs) = insert (identity xs) front

stage : ∀ {x : A} {xs ys} → Perm (x ∷ xs) ys →
        Σ (List A) λ zs → Perm xs zs × Perm (x ∷ zs) ys
stage {xs = xs} p = xs , identity xs , p

collapse : ∀ {x : A} {xs ys} → (Σ (List A) λ zs → Perm xs zs × Perm (x ∷ zs) ys) → Perm (x ∷ xs) ys
collapse (_ , tail , finish) = compose (insert tail front) finish
