{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.RallyRoute where

open import AoP.Common.Prelude
open import AoP.Chapter08.RallyDominance
open import AoP.Common.NatOrder using (rid; chain)
open import Agda.Builtin.Nat using (Nat)

-- A station supplies fuel before its outgoing leg. A run records only
-- legal journeys, so truncated subtraction never hides an empty tank.
record Station : Set where
  constructor station
  field supply distance : Nat

module Routes (capacity : Nat) where
  data Run : List Station → State → State → Set where
    end : ∀ x → Run [] x x
    drive : ∀ {s d xs x y} a → Leg.Allowed capacity s d a x →
            Run xs (Leg.arrive capacity s d a x) y → Run (station s d ∷ xs) x y

  -- Replay an arbitrary remaining itinerary. Every step of the old
  -- driver is also possible for the new one with no more stops and
  -- at least as much fuel. The final states satisfy the same bound.
  replay : ∀ {xs x y z} → Better x y → Run xs y z → Σ State λ w → Run xs x w × Better w z
  replay better (end y) = _ , end _ , better
  replay better (drive {s} {d} a legal rest) with Leg.simulate capacity s d a _ _ better legal
  ... | can , improved with replay improved rest
  ...   | w , run , bound = w , drive a can run , bound
