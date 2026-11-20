{-# OPTIONS --safe --without-K #-}
module AoP.RallyCoverage where

open import AoP.Prelude
open import AoP.RallyDominance
open import AoP.RallyFrontier using (module Pruning; module Search)
open import AoP.RallyRoute using (module Routes; station)
open import AoP.RallyExpansion using (module Law)
open import AoP.Subsequences using (_∈_; here)
open import AoP.Thinning using (Thin)
open import AoP.NatOrder using (rid)
open import Agda.Builtin.Nat using (Nat)

module Coverage (cap : Nat) where
  open Search cap
  open Routes cap
  -- Start from a frontier containing a replacement for the competing
  -- driver's state. After one leg, pruning supplies another replacement;
  -- the induction hypothesis then applies to the remaining itinerary.
  follow : ∀ {legs y z} → Run legs y z → ∀ xs {x} → x ∈ xs → Better x y →
           Σ State λ w → (w ∈ scan legs xs) × Better w z
  follow (end _) xs {x} m dom = x , m , dom
  follow (drive {s} {d} a legal rest) xs {x} m dom with Leg.simulate cap s d a x _ dom legal
  ... | ok , improved with Thin.cover (Pruning.correct (Move.expand s d xs)) _ (Law.complete cap s d xs m a ok)
  ...   | u , kept , (cheap , full) = follow rest _ kept (chain′ (cheap , full) improved)
    where chain′ : ∀ {u v w} → Better u v → Better v w → Better u w
          chain′ (p , q) (r , t) = AoP.NatOrder.chain p r , AoP.NatOrder.chain t q

  complete : ∀ {legs x z} → Run legs x z → Σ State λ w → (w ∈ scan legs (x ∷ [])) × Better w z
  complete run = follow run _ here (rid _ , rid _)
