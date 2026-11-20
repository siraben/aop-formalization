{-# OPTIONS --safe --without-K #-}
module AoP.RallyMinimum where

open import AoP.Prelude
open import AoP.RallyDominance
open import AoP.RallyRoute using (Station; station; module Routes)
open import AoP.RallyFrontier using (module Search)
open import AoP.RallyReachable using (module Sound)
open import AoP.RallyCoverage using (module Coverage)
open import AoP.FiniteMinimum using () renaming (module Search to Minimum)
open import AoP.NatOrder using (_≤_; chain)
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (inl)
open import Agda.Builtin.Nat using (Nat)

-- Select a cheapest arrival and reconstruct its itinerary. If the
-- frontier is empty, coverage rules out every feasible arrival.
module Solver (cap : Nat) where
  open Routes cap
  open Search cap
  open State
  module M = Minimum (λ (_ : State) → ⊤) (λ _ → inl tt) stops
  data Answer (legs : List Station) (x : State) : Set where
    impossible : (∀ y → Run legs x y → ⊥) → Answer legs x
    optimal : (w : State) → Run legs x w → (∀ z → Run legs x z → stops w ≤ stops z) → Answer legs x

  solve : ∀ legs x → Answer legs x
  solve legs x with M.scan (scan legs (x ∷ []))
  ... | M.none no = impossible λ y run → let w , m , _ = Coverage.complete cap run in no w m tt
  ... | M.best w m _ least = optimal w (Sound.reachable cap legs x m) λ z run →
    let v , mem , better = Coverage.complete cap run in chain (least v mem tt) (fst better)
