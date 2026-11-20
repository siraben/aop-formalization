{-# OPTIONS --safe --without-K #-}
module AoP.LatenessExchange where

open import AoP.SignedLateness using (charge)
open import AoP.Tardiness using (Job)
open import AoP.SignedSegment using (_≤_; chain; pp; repeat-mono; down; down-mono)
import AoP.NatOrder as N
open import AoP.ScheduleExchange using (module Law)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Agda.Builtin.Int using (Int)
open Job

-- The exchange proof only needs earlier completion to preserve each
-- job's threshold. Subtracting a fixed weighted deadline preserves the
-- integer order, including when one completion is early and one late.
private
  weighted : ∀ w {s t} → s N.≤ t → (w * s) N.≤ (w * t)
  weighted 0 p = N.z≤
  weighted (suc w) p = N.sum-mono p (weighted w p)

monotone : ∀ j {s t} → s N.≤ t → charge j s ≤ charge j t
monotone j p = repeat-mono (weight j * due j) down down-mono (pp (weighted (weight j) p))

module Limit (limit : Int) where
  Allowed : Job → Nat → Set
  Allowed j t = charge j t ≤ limit
  open Law duration Allowed (λ j p ok → chain (monotone j p) ok) public
