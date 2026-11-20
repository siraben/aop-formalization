{-# OPTIONS --safe --without-K #-}
module AoP.WeightedDepthSpec where

open import AoP.Prelude
open import AoP.Trees using (Tree; tip; bin)
open import AoP.WeightedPaths using (Pair; lift; merge; scan; distribute)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

-- Exercise 3.14. Specify the answer directly in terms of tip depths:
-- a tip reached at depth d contributes d * w. This specification
-- passes depth down the tree; the derived scan returns summaries up it.
at-depth : Nat → Tree Nat → Pair
at-depth d (tip w) = w , d * w
at-depth d (bin l r) = merge (at-depth (suc d) l) (at-depth (suc d) r)

-- Increasing the starting depth by one adds the weight of every tip
-- once. At a fork, distributivity collects both increases into one.
shift : ∀ d t → at-depth (suc d) t ≡ lift (at-depth d t)
shift d (tip w) = refl
shift d (bin l r) rewrite shift (suc d) l | shift (suc d) r = distribute (at-depth (suc d) l) (at-depth (suc d) r)

correct : ∀ t → at-depth 0 t ≡ scan t
correct (tip w) = refl
correct (bin l r) rewrite shift 0 l | shift 0 r | correct l | correct r = distribute (scan l) (scan r)

-- The right fork contributes 8 at its own root. Its parent adds one
-- edge for weights 3 and 5 there, and one edge for the left tip of 2.
example : at-depth 0 (bin (tip 2) (bin (tip 3) (tip 5))) ≡ (10 , 18)
example = begin
  at-depth 0 (bin (tip 2) (bin (tip 3) (tip 5))) ≡⟨ correct (bin (tip 2) (bin (tip 3) (tip 5))) ⟩
  lift (merge (2 , 0) (lift (merge (3 , 0) (5 , 0)))) ≡⟨⟩
  lift (merge (2 , 0) (8 , 8)) ≡⟨⟩
  lift (10 , 8) ≡⟨⟩ (10 , 18) ∎
