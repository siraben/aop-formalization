{-# OPTIONS --safe --without-K #-}
module AoP.BusFrontierSound where

open import AoP.Prelude
open import AoP.BusProfile using (Stops; sites; add)
open import AoP.BusFrontier using (module Generate)
open import AoP.BusProfileDecision using (module Frontier)
open import AoP.BusLayouts using (Layout; take; done; skip)
open import AoP.Subsequences using (_∈_; here; there; split; preimage)
open import AoP.Thinning using (Thin)
open import AoP.Polynomial using (inl; inr)
open import AoP.Horner using (map)
open import AoP.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; suc)

stops : Stops → List Nat
stops (sites x xs) = x ∷ xs

module Law (demand : List Nat) where
  open Generate demand
  open Frontier.Thin demand using (correct)
  -- Pruning only discards. Recover a take/skip derivation for every
  -- survivor: taking j consumes one quota slot, skipping consumes none.
  valid : ∀ j m k {l} → l ∈ build j m k → Layout j m (suc k) (stops l)
  valid j (suc m) 0 member with Thin.subset (correct (sites j [] ∷ build (suc j) m 0)) member
  ... | here = take done
  ... | there old = skip (valid (suc j) m 0 old)
  valid j (suc m) (suc k) member with split new old (Thin.subset (correct (new ++ old)) member)
    where new = map (add j) (build (suc j) m k)
          old = build (suc j) m (suc k)
  ... | inr q = skip (valid (suc j) m (suc k) q)
  ... | inl q with preimage (add j) (build (suc j) m k) q
  ...   | sites x xs , p , refl = take (valid (suc j) m k p)
