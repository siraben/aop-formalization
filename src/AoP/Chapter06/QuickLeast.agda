{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.QuickLeast where

open import AoP.Common.Prelude
open import AoP.Chapter06.Quicksort
open import AoP.Chapter06.QuickFusion using (output)
open import AoP.Chapter06.QuickEquation using (join; fork-case; empty-case; children)
open import AoP.Chapter06.SelectionSort using (length)
open import AoP.Common.NatOrder using (_≤_; rid; s≤; chain)
open import AoP.Chapter04.Relations using (_←_; _⊆_)
open import AoP.Chapter04.Shunting using (graph)
open import Agda.Builtin.Nat using (Nat; suc)

-- The two summands of the quicksort recurrence: on empty input return
-- []; otherwise relate each child to an output, then join at the pivot.
L = List Nat
child : (L ← L) → L × (Nat × L) → L → Set
child X (l , p , r) ys = Σ L λ u → Σ L λ v → X u l × (X v r × (join p u v ≡ ys))

Step : (L ← L) → L ← L
Step X ys [] = [] ≡ ys
Step X ys (x ∷ xs) = child X (output x xs) ys

apply : ∀ x xs → let l , p , r = output x xs in
        children x xs ≡ join p (quicksort l) (quicksort r)
apply x xs with split x xs
... | p , l , r , _ = refl

equation : ∀ x xs → let l , p , r = output x xs in
           quicksort (x ∷ xs) ≡ join p (quicksort l) (quicksort r)
equation x xs = fork-case x xs ∙ apply x xs

fold : Step (graph quicksort) ⊆ graph quicksort
fold {a = []} e = e
fold {a = x ∷ xs} (_ , _ , refl , refl , e) = equation x xs ∙ e

unfold-law : graph quicksort ⊆ Step (graph quicksort)
unfold-law {a = []} e = e
unfold-law {a = x ∷ xs} refl with equation x xs
... | eq = _ , _ , refl , refl , back eq
  where back : ∀ {a b : L} → a ≡ b → b ≡ a
        back refl = refl

-- Every pre-fixed relation contains the executable graph: the induction
-- budget bounds input length, so both recursive hypotheses are available
-- at each split. No totality or single-valuedness assumption on X.
module Least (X : L ← L) (closed : Step X ⊆ X) where
  bounds : ∀ x xs → let l , p , r = output x xs in
           (length l ≤ length xs) × (length r ≤ length xs)
  bounds x xs with split x xs
  ... | p , l , r , s with smaller s
  ...   | s≤ lb , s≤ rb = lb , rb

  accept : ∀ n xs → length xs ≤ n → X (quicksort xs) xs
  accept n [] _ = closed {a = []} refl
  accept (suc n) (x ∷ xs) (s≤ fuel) = closed {a = x ∷ xs}
    (_ , _ , accept n _ (chain (fst (bounds x xs)) fuel) ,
             accept n _ (chain (snd (bounds x xs)) fuel) , back (equation x xs))
    where back : ∀ {a b : L} → a ≡ b → b ≡ a
          back refl = refl

  least : graph quicksort ⊆ X
  least {a = xs} refl = accept (length xs) xs (rid _)
