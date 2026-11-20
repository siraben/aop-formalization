{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.QuickSplitRefinement where

open import AoP.Common.Prelude
open import AoP.Chapter06.QuickSplitFold using (Parts; base; step; fold⁺)
open import AoP.Chapter06.QuickOrdered using (Upper; end; next)
open import AoP.Chapter06.Selection using (Lower; empty; below)
open import AoP.Chapter05.Permutations using (Perm; insert; front; later)
open import AoP.Chapter05.PermuteTail using (identity)
open import AoP.Chapter06.QuickPermutation using (skip)
open import AoP.Common.NatOrder using (compare)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat)

-- §6.6. The two provisos for deriving split itself: a singleton
-- starts a guarded permutation, and cons preserves the specification
-- for ANY admissible tail partition, not just the one the fold chose.
Valid : List Nat → Parts → Set
Valid xs (p , l , r) = Upper p l × Lower p r × Perm xs (l ++ (p ∷ r))
start : ∀ x → Valid (x ∷ []) (base x)
start x = end , empty , identity _
advance : ∀ x xs t → Valid xs t → Valid (x ∷ xs) (step x t)
advance x xs (p , l , r) (up , lo , perm) with compare x p
... | inl xp = next xp up , lo , insert perm front
... | inr px = up , below px lo , insert perm (skip l (later front))

correct : ∀ x xs → Valid (x ∷ xs) (fold⁺ base step x xs)
correct x [] = start x
correct x (y ∷ ys) = advance x (y ∷ ys) _ (correct y ys)
