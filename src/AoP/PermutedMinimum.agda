{-# OPTIONS --safe --without-K #-}
module AoP.PermutedMinimum where

open import AoP.Prelude
open import AoP.Trees using (Tree)
open import AoP.BracketSpine using (leaves)
open import AoP.Permutations using (Perm)
open import AoP.PermuteTail using (identity)
open import AoP.PermutedBrackets using (module Search)
open import AoP.BracketMinimum using (module Solve)
open import AoP.FiniteMinimum using () renaming (module Search to Minimum)
open import AoP.NatOrder using (_≤_)
open import AoP.Polynomial using (inl)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 9.15. The competitor is any tree using exactly the input
-- occurrences. Its cost need not be invariant under rearrangement.
module Optimize {A : Set} (cost : Tree A → Nat) where
  open Search {A}
  module M = Minimum (λ (_ : Tree A) → ⊤) (λ _ → inl tt) cost
  feasible : ∀ x xs → Σ (Tree A) λ t → Perm (x ∷ xs) (leaves t)
  feasible x xs with Solve.witness cost x xs
  ... | t , eq = t , from-equal eq
    where from-equal : ∀ {as bs : List A} → as ≡ bs → Perm bs as
          from-equal refl = identity _

  solve : ∀ x xs → Σ (Tree A) λ t → Perm (x ∷ xs) (leaves t) ×
                    (∀ u → Perm (x ∷ xs) (leaves u) → cost t ≤ cost u)
  solve x xs with M.scan (trees (x ∷ xs))
  ... | M.best t m _ opt = t , sound _ m , λ u p → opt u (complete u p) tt
  ... | M.none no with feasible x xs
  ...   | t , p with no t (complete t p) tt
  ...     | ()
