{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.RallyDominance where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; chain; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_)

-- Exercise 8.30. At each station the driver either passes or stops
-- and takes as much supplied fuel as fits. Then the driver must have
-- enough fuel to reach the next station. Both distance and fuel use
-- natural units. A route begins with a tank level within capacity.
cap-at : Nat → Nat → Nat
cap-at 0 _ = 0
cap-at (suc c) 0 = 0
cap-at (suc c) (suc f) = suc (cap-at c f)
private
  cap-mono : ∀ c {x y} → x ≤ y → cap-at c x ≤ cap-at c y
  cap-mono 0 p = z≤
  cap-mono (suc c) z≤ = z≤
  cap-mono (suc c) (s≤ p) = s≤ (cap-mono c p)
  spend-mono : ∀ d {x y} → x ≤ y → x - d ≤ y - d
  spend-mono 0 p = p
  spend-mono (suc d) z≤ = z≤
  spend-mono (suc d) (s≤ p) = spend-mono d p

record State : Set where
  constructor at
  field stops fuel : Nat
open State
Better : State → State → Set
Better x y = (stops x ≤ stops y) × (fuel y ≤ fuel x)

data Action : Set where pass refill : Action
module Leg (capacity supply distance : Nat) where
  load : Action → Nat → Nat
  load pass f = f
  load refill f = cap-at capacity (f + supply)
  count : Action → Nat → Nat
  count pass n = n
  count refill n = suc n
  Allowed : Action → State → Set
  Allowed a x = distance ≤ load a (fuel x)
  arrive : Action → State → State
  arrive a (at n f) = at (count a n) (load a f - distance)
  private
    loaded : ∀ a {x y} → x ≤ y → load a x ≤ load a y
    loaded pass p = p
    loaded refill p = cap-mono capacity (sum-mono p (rid supply))
    counted : ∀ a {n m} → n ≤ m → count a n ≤ count a m
    counted pass p = p
    counted refill p = s≤ p

  simulate : ∀ a x y → Better x y → Allowed a y → Allowed a x × Better (arrive a x) (arrive a y)
  simulate a x y (cheaper , fuller) legal = chain legal (loaded a fuller) , counted a cheaper , spend-mono distance (loaded a fuller)
