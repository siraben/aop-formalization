{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.BusFrontier where

open import AoP.Common.Prelude
open import AoP.Chapter08.BusProfile using (Stops; sites; add)
open import AoP.Chapter08.BusProfileDecision using (module Frontier)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter03.Horner using (map)
open import Agda.Builtin.Nat using (Nat; suc)

-- Frontiers are indexed by a positive quota: k denotes k + 1 stops.
-- At block j, taking the first stop creates a singleton at quota one;
-- at larger quotas it extends a smaller suffix layout. Skipping j
-- preserves the quota. Only compare candidates within that same quota.
module Generate (demand : List Nat) where
  open Frontier.Thin demand using (thinlist)
  build : Nat → Nat → Nat → List Stops
  build j 0 k = []
  build j (suc m) 0 = thinlist (sites j [] ∷ build (suc j) m 0)
  build j (suc m) (suc k) = thinlist (map (add j) (build (suc j) m k) ++ build (suc j) m (suc k))

-- Two stops among 0,1,2, demand only at 2. Both [0,2] and
-- [1,2] give distance zero; a single representative suffices.
example : Generate.build (2 ∷ []) 0 3 1 ≡ sites 0 (2 ∷ []) ∷ []
example = refl
