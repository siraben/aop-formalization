{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.RallyMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter08.RallyDominance
open import AoP.Chapter08.RallyRoute using (Station; station; module Routes)
open import AoP.Chapter08.RallyFrontier using (module Search)
open import AoP.Chapter08.RallyReachable using (module Sound)
open import AoP.Chapter08.RallyCoverage using (module Coverage)
open import AoP.Common.FiniteMinimum using () renaming (module Search to Minimum)
open import AoP.Common.NatOrder using (_≤_; chain)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter02.Polynomial using (inl)
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
