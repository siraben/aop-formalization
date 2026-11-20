{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.GreedyTardinessCost where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (max)
open import AoP.Common.NatOrder using (_≤_; rid; z≤; s≤; chain)
open import AoP.Chapter10.Tardiness using (Job)
open import AoP.Chapter10.TardinessBound using (charge; module Limit)
open import AoP.Chapter10.BackwardSchedule using (Run)
open import AoP.Chapter10.BackwardOptimal using (module Threshold)
open import AoP.Chapter05.Permutations using (Perm)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- §10.3. Turn the threshold result into a numerical inequality. Evaluate
-- a schedule from left to right with its actual start time s. A bound on
-- the maximum means exactly that the first charge and every tail charge
-- obey that bound. Choose the competitor's own maximum as the threshold.
peak : Nat → List Job → Nat
peak s [] = 0
peak s (j ∷ js) = let t = s + Job.duration j in max (charge j t) (peak t js)

private
  lub : ∀ {a b k} → a ≤ k → b ≤ k → max a b ≤ k
  lub z≤ q = q
  lub (s≤ p) z≤ = s≤ p
  lub (s≤ p) (s≤ q) = s≤ (lub p q)

  left : ∀ a b → a ≤ max a b
  left zero b = z≤
  left (suc a) zero = rid _
  left (suc a) (suc b) = s≤ (left a b)

  right : ∀ a b → b ≤ max a b
  right zero b = rid _
  right (suc a) zero = z≤
  right (suc a) (suc b) = s≤ (right a b)

module Cap (k : Nat) where
  open Limit k
  fits→bound : ∀ {s js} → Fits s js → peak s js ≤ k
  fits→bound empty = z≤
  fits→bound (step p tail) = lub p (fits→bound tail)

  bound→fits : ∀ s js → peak s js ≤ k → Fits s js
  bound→fits s [] le = empty
  bound→fits s (j ∷ js) le = step (chain (left a b) le) (bound→fits t js (chain (right a b) le))
    where t = s + Job.duration j; a = charge j t; b = peak t js

optimal : ∀ {jobs out competitor} → Run jobs out → Perm jobs competitor → peak 0 out ≤ peak 0 competitor
optimal {competitor = c} run perm = Cap.fits→bound k
  (Threshold.transport-run k run perm (Cap.bound→fits k 0 c (rid k)))
  where k = peak 0 c
