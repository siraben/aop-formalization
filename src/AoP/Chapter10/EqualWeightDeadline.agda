{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.EqualWeightDeadline where

open import AoP.Common.Prelude
open import AoP.Chapter10.Tardiness using (Job; job)
open import AoP.Chapter10.TardinessBound using (charge)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; sum-mono; weaken; chain)
open import Agda.Builtin.Nat using (Nat; suc; _-_; _*_)

-- Exercise 10.9. Compare candidates for the LAST position. Every
-- candidate finishes at the same total time, so with a common weight
-- the latest due date gives a least final penalty, independently of
-- duration. Truncation allows ties even for different due dates.
private
  slack : ∀ t d → t - d ≤ t
  slack 0 0 = z≤
  slack 0 (suc d) = z≤
  slack (suc t) 0 = rid _
  slack (suc t) (suc d) = weaken (slack t d)
  later : ∀ t {a b} → a ≤ b → t - b ≤ t - a
  later 0 {b = b} z≤ = slack 0 b
  later 0 (s≤ le) = z≤
  later (suc t) {b = b} z≤ = slack (suc t) b
  later (suc t) (s≤ le) = later t le
  scale : ∀ w {a b} → a ≤ b → a * w ≤ b * w
  scale w z≤ = z≤
  scale w (s≤ le) = sum-mono (rid w) (scale w le)

least-charge : ∀ x y t → Job.weight x ≡ Job.weight y → Job.due x ≤ Job.due y → charge y t ≤ charge x t
least-charge (job dx a w) (job dy b .w) t refl le = scale w (later t le)
