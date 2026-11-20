{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.PartyRootRefinement where

open import AoP.Common.Prelude
open import AoP.Chapter07.PartyChoiceOrder using (module Law)
open import AoP.Chapter08.Thinning using (Min)

-- §7.3. The order R puts the better guest list first, so Min R
-- expresses maximum conviviality. A root candidate is a pair of lists
-- (include, exclude). This calculation justifies moving the final
-- choice *after* maximizing the pair, before optimizing the tree fold.
module Derive {A : Set} (R : A → A → Set)
  (trans : ∀ {x y z} → R x y → R y z → R x z) where
  open Law R
  module At (pool : Pair → Set) where
    Parties : A → Set
    Parties x = Σ Pair λ p → pool p × Choose x p
    -- Any rival party arose from one side of a feasible pair. Match
    -- that same side in the winning pair; the root choice beats this
    -- matched party, which in turn beats the original rival.
    refine : ∀ {p x} → Min Better p pool → Min R x (λ y → Choose y p) → Min R x Parties
    refine {p} (valid , pair-best) (chosen , root-best) = (p , valid , chosen) , wins
      where
        wins : ∀ y → Parties y → R _ y
        wins y (q , feasible , side) with match (pair-best q feasible) side
        ... | z , corresponding , bound = trans (root-best z corresponding) bound
