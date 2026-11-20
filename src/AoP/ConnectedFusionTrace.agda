{-# OPTIONS --safe --without-K #-}
module AoP.ConnectedFusionTrace where

open import AoP.Prelude
open import AoP.Snoc using (ε; _▻_)
open import AoP.ConnectedPartitionTrace using (Point; low; left; right; _≤_; same; trans; cmp)
open import AoP.ConnectedPartitionFusion using (module Fusion)
open Fusion _≤_ (λ _ → same) trans cmp

-- Observe the actual streaming state: completed minima, active block
-- (newest first), and active minimum. A cut is forced by right versus
-- left, even though right is comparable with the current minimum low.
record View : Set where
  constructor row
  field saved : AoP.Snoc.Snoc Point
        newest-first : List Point
        least : Point
observe : State Point → List View
observe empty = []
observe (active ds b) = row ds (Block.xs b) (Block.m b) ∷ []
start : observe (fused (ε ▻ left)) ≡ row ε (left ∷ []) left ∷ []
start = refl
grow : observe (fused (ε ▻ left ▻ low)) ≡ row ε (low ∷ left ∷ []) low ∷ []
grow = refl
cut : observe (fused (ε ▻ left ▻ low ▻ right)) ≡ row (ε ▻ low) (right ∷ []) right ∷ []
cut = refl
finish-trace : thinlist (ε ▻ left ▻ low ▻ right) ≡ ε ▻ low ▻ right
finish-trace = refl
