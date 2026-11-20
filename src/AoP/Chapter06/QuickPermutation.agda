{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.QuickPermutation where

open import AoP.Common.Prelude
open import AoP.Chapter06.Quicksort
open import AoP.Chapter05.Permutations using (Perm; empty; insert; Insert; front; later)
open import AoP.Chapter10.PermuteRemoval using (remove-permuted)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (rid)
open import AoP.Chapter06.SelectionSort using (length)
open import Agda.Builtin.Nat using (Nat)
private variable A : Set

-- First calculate the intermediate permutation for partitioning. Sending
-- an occurrence right moves it across the whole left side and the pivot.
skip : ∀ (ls : List A) {a xs ys} → Insert a xs ys → Insert a (ls ++ xs) (ls ++ ys)
skip [] i = i
skip (x ∷ ls) i = later (skip ls i)

partition : ∀ {p xs l r} → Split p xs l r → Perm xs (l ++ (p ∷ r))
partition (pivot _) = insert empty front
partition (left le s) = insert (partition s) front
partition (right {l = l} ge s) = insert (partition s) (skip l (later front))

compose : ∀ {xs ys zs : List A} → Perm xs ys → Perm ys zs → Perm xs zs
compose empty empty = empty
compose (insert p i) q with remove-permuted i q
... | ws , residual , pos = insert (compose p residual) pos

append-pos : ∀ {a : A} {xs ys} → Insert a xs ys → ∀ zs → Insert a (xs ++ zs) (ys ++ zs)
append-pos front zs = front
append-pos (later i) zs = later (append-pos i zs)

append-perm : ∀ {xs ys us vs : List A} → Perm xs ys → Perm us vs → Perm (xs ++ us) (ys ++ vs)
append-perm empty q = q
append-perm (insert p i) q = insert (append-perm p q) (append-pos i _)

-- Flatten a fork: first partition, then independently reorder its left
-- and right children. The pivot stays between them. Composing these
-- permutations gives a witness for every occurrence in the original list.
flatten-perm : ∀ {xs} (t : Tree xs) → Perm xs (flatten t)
flatten-perm null = empty
flatten-perm (fork p s l r) = compose (partition s) (append-perm (flatten-perm l) (insert (flatten-perm r) front))

preserves : ∀ xs → Perm xs (quicksort xs)
preserves xs = flatten-perm (unfold (length xs) xs (rid _))
