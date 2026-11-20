{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.LayeredCostFold where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)

-- §8.2. When prepending a vertex the cost update needs the head of
-- the old path. Fold into (path,cost) so the head is available.
module Paths {V : Set} (weight : V → V → Nat) where
  data Path : Set where
    single : V → Path
    via : V → Path → Path
  head : Path → V
  head (single v) = v
  head (via v p) = v
  cost : Path → Nat
  cost (single v) = 0
  cost (via v p) = weight v (head p) + cost p
  fold : ∀ {B : Set} → (V → B) → (V → B → B) → Path → B
  fold z s (single v) = z v
  fold z s (via v p) = s v (fold z s p)
  step : V → Path × Nat → Path × Nat
  step v (p , n) = via v p , weight v (head p) + n
  scan = fold (λ v → single v , 0) step
  exact : ∀ p → scan p ≡ (p , cost p)
  exact (single v) = refl
  exact (via v p) = cong (step v) (exact p)

-- Four vertices in three layers: {root}, {west,east}, {goal}.
-- Discarding the dearer suffix at the middle layer loses the optimum.
data V : Set where root west east goal : V
weight : V → V → Nat
weight root west = 10
weight root east = 1
weight west goal = 2
weight east goal = 5
weight _ _ = 0
open Paths weight
w e : Path
w = via west (single goal)
e = via east (single goal)
pair : Nat → Nat → Nat × Nat
pair x y = x , y
suffixes : pair (snd (scan w)) (snd (scan e)) ≡ (2 , 5)
suffixes = refl
complete-paths : pair (snd (scan (via root w))) (snd (scan (via root e))) ≡ (12 , 6)
complete-paths = refl
