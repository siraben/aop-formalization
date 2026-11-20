{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.CylinderPotential where

open import AoP.Common.Prelude
open import AoP.Chapter07.Cylinder using (module Grid)
open import AoP.Common.NatOrder using (_≤_; rid; chain; sum-mono)
open import Agda.Builtin.Nat using (_+_)

-- A way to audit a shortest-path answer without normalizing the search.
-- Label each cell by a proposed lower bound. At the exit compare with
-- the cell charge; elsewhere check one inequality per outgoing edge.
-- Induction along any rival path then adds up those local inequalities.
module Audit (Row : Set) (up down : Row → Row) where
  open Grid Row up down
  data Labels : Column → List Column → Column → Set where
    end : ∀ {c v} → (∀ r → v r ≤ c r) → Labels c [] v
    step : ∀ {c d ds v w} → Labels d ds w →
      (∀ r → v r ≤ c r + w (up r)) →
      (∀ r → v r ≤ c r + w r) →
      (∀ r → v r ≤ c r + w (down r)) → Labels c (d ∷ ds) v

  lower : ∀ {c cs v} → Labels c cs v → ∀ r (p : Path cs) → v r ≤ cost c r p
  lower (end ok) r exit = ok r
  lower (step tail u s d) r (rise p) = chain (u r) (sum-mono (rid _) (lower tail (up r) p))
  lower (step tail u s d) r (stay p) = chain (s r) (sum-mono (rid _) (lower tail r p))
  lower (step tail u s d) r (fall p) = chain (d r) (sum-mono (rid _) (lower tail (down r) p))

  -- One attaining route suffices. Labels on other rows only need to
  -- be lower bounds, provided none is below the claimed optimum.
  certify : ∀ {c cs v r} (p : Path cs) → Labels c cs v →
    (∀ s → cost c r p ≤ v s) → ∀ s (q : Path cs) → cost c r p ≤ cost c s q
  certify p labels first s q = chain (first s) (lower labels s q)
