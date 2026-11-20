{-# OPTIONS --safe --without-K #-}
module AoP.RallyPartialRoute where

open import AoP.Prelude
open import AoP.RallyDominance
open import AoP.RallyPartialLoad using (module Law)
open import AoP.RallyRoute using (Station; station; module Routes)
open import AoP.NatOrder using (_≤_; rid; chain)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_)
open State

module Flexible (c : Nat) where
  open Routes c
  -- In the larger specification a paid stop chooses the departure
  -- level, subject to the fuel already present, local supply and cap.
  data Journey : List Station → State → State → Set where
    finish : ∀ x → Journey [] x x
    bypass : ∀ {s d x z legs} → Leg.Allowed c s d pass x →
             Journey legs (Leg.arrive c s d pass x) z → Journey (station s d ∷ legs) x z
    pickup : ∀ {s d x z legs} f → fuel x ≤ f → f ≤ c → f ≤ fuel x + s → d ≤ f →
             Journey legs (at (suc (stops x)) (f - d)) z → Journey (station s d ∷ legs) x z

  match : ∀ {legs x y z} → Better x y → Journey legs y z → Σ State λ w → Run legs x w × Better w z
  match {x = x} b (finish _) = x , end x , b
  match b (bypass {s} {d} legal rest) with Leg.simulate c s d pass _ _ b legal
  ... | can , improved with match improved rest
  ...   | w , run , bound = w , drive pass can run , bound
  match b (pickup {s} {d} f lo hi available enough rest) with Law.partial c s d _ _ f b lo hi available enough
  ... | can , improved with match improved rest
  ...   | w , run , bound = w , drive refill can run , bound

  -- Transfer the full-refill solver's cost bound to every flexible
  -- competitor, keeping its original executable itinerary as witness.
  transfer : ∀ {legs x} (n : Nat) → (∀ w → Run legs x w → n ≤ stops w) →
             ∀ z → Journey legs x z → n ≤ stops z
  transfer n least z journey with match (rid _ , rid _) journey
  ... | w , run , bound = chain (least w run) (fst bound)
