{-# OPTIONS --safe --without-K #-}
module AoP.QuickFusion where

open import AoP.Prelude
open import AoP.Quicksort using (split; Split)
open import AoP.QuickPermutation using (partition)
open import AoP.QuickOrdered using (bounds; Upper; end; next; convert)
open import AoP.SetSort using (backward-perm; lower)
open import AoP.PivotFusion using (module Proviso)
open import AoP.PivotPermutation using (module Pivot)
open import AoP.NatOrder using (_≤_)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Relations using (_←_; _⊆_)
open import Agda.Builtin.Nat using (Nat)

-- Instantiate the fusion proviso with the *computed* split. For a
-- nonempty input `split` returns its pivot, left and right lists, and a
-- trace. Forgetting the trace gives the partial graph used below. Empty
-- input is handled by the null case of the tree hylomorphism.
open Pivot {Nat} using (Triple)
open Proviso _≤_ using (Eligible; module Law)

output : Nat → List Nat → Triple
output x xs with split x xs
... | p , l , r , _ = l , p , r

data Cut : Triple ← List Nat where
  cut : ∀ x xs → Cut (output x xs) (x ∷ xs)

upper : ∀ {a p xs} → Upper p xs → a ∈ xs → a ≤ p
upper (next le _) here = le
upper (next _ tail) (there m) = upper tail m

correct : Cut ⊆ Eligible
correct (cut x xs) with split x xs
... | p , l , r , trace with bounds trace
...   | lo , hi = ((λ m → upper lo m) , (λ m → lower hi m)) , backward-perm (convert (partition trace))

open Law Cut correct public using () renaming (fusion to executable-fusion)
