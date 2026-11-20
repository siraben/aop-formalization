{-# OPTIONS --safe --without-K #-}
module AoP.RallyPartialLoad where

open import AoP.Prelude
open import AoP.RallyDominance
open import AoP.NatOrder using (_≤_; rid; chain; z≤; s≤; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_)
open State

-- A driver paying for a stop may take less than the available supply.
-- The departure tank level then lies between the old level and BOTH
-- upper bounds: capacity and old fuel plus the station supply.
under-cap : ∀ {f c x} → f ≤ c → f ≤ x → f ≤ cap-at c x
under-cap {c = 0} z≤ q = z≤
under-cap {c = suc c} {0} p z≤ = z≤
under-cap {c = suc c} {suc x} z≤ q = z≤
under-cap {c = suc c} {suc x} (s≤ p) (s≤ q) = s≤ (under-cap p q)

private
  spend : ∀ d {x y} → x ≤ y → x - d ≤ y - d
  spend 0 p = p
  spend (suc d) z≤ = z≤
  spend (suc d) (s≤ p) = spend d p

module Law (c s d : Nat) where
  open Leg c s d
  partial : ∀ x y f → Better x y → fuel y ≤ f → f ≤ c → f ≤ fuel y + s → d ≤ f →
            Allowed refill x × Better (arrive refill x) (at (suc (stops y)) (f - d))
  partial x y f (cheap , full) _ fits available enough = chain enough upper , s≤ cheap , spend d upper
    where upper : f ≤ cap-at c (fuel x + s)
          upper = under-cap fits (chain available (sum-mono full (rid s)))
