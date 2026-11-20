{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.DeadlineRunCount where

open import AoP.Common.Prelude
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Chapter10.DeadlineMerge using (merge)
open import AoP.Chapter10.DeadlineMergeRound using (Runs; Pass; round)
open import AoP.Common.NatOrder using (_≤_; s≤; z≤)
open import Agda.Builtin.Nat using (Nat; suc)

-- Pair adjacent runs, carrying an odd last run. One round takes the
-- ceiling half, including the boundary cases of zero and one run.
half-up : Nat → Nat
half-up 0 = 0
half-up 1 = 1
half-up (suc (suc n)) = suc (half-up n)

count : ∀ rs → len (Pass.out (round rs)) ≡ half-up (len rs)
count [] = refl
count (_ ∷ []) = refl
count (x ∷ y ∷ rs) with merge x y | round rs | count rs
... | _ , _ | _ | eq = cong suc eq

double : Nat → Nat
double 0 = 0
double (suc n) = suc (suc (double n))

fits : ∀ n m → n ≤ double m → half-up n ≤ m
fits 0 m le = z≤
fits 1 (suc m) le = s≤ z≤
fits (suc (suc n)) (suc m) (s≤ (s≤ le)) = s≤ (fits n m le)

power : Nat → Nat
power 0 = 1
power (suc k) = double (power k)

-- With room for 2^k runs, k rounds suffice to leave at most one.
passes : Nat → Runs → Runs
passes 0 rs = rs
passes (suc k) rs = passes k (Pass.out (round rs))

one : ∀ k rs → len rs ≤ power k → len (passes k rs) ≤ 1
one 0 rs bound = bound
one (suc k) rs bound = one k _ (step rs bound)
  where step : ∀ us → len us ≤ power (suc k) → len (Pass.out (round us)) ≤ power k
        step us b rewrite count us = fits (len us) (power k) b
