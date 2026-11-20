{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.RallyFrontier where

open import AoP.Common.Prelude
open import AoP.Chapter08.RallyDominance
open import AoP.Chapter08.RallyRoute using (Station; station)
open import AoP.Chapter08.Bump using (module Prune)
open import AoP.Common.NatOrder using (rid; chain)
open import AoP.Chapter08.ParagraphMinimum using (le?; Dec)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat)
open State

better? : ∀ x y → Dec (Better x y)
better? x y with le? (stops x) (stops y) | le? (fuel y) (fuel x)
... | inl p | inl q = inl (p , q)
... | inr no | _ = inr (λ b → no (fst b))
... | inl _ | inr no = inr (λ b → no (snd b))
module P = Prune Better (λ x → rid _ , rid _) (λ p q → chain (fst p) (fst q) , chain (snd q) (snd p))
compare : ∀ x y → P.Comparison x y
compare x y with better? x y
... | inl p = P.first p
... | inr _ with better? y x
...   | inl p = P.second p
...   | inr _ = P.retain
module Pruning = P.Algorithm compare

module Search (capacity : Nat) where
  module Move (s d : Nat) where
    open Leg capacity s d
    try : Action → State → List State → List State
    try a x rest with le? d (load a (fuel x))
    ... | inl _ = arrive a x ∷ rest
    ... | inr _ = rest
    expand : List State → List State
    expand [] = []
    expand (x ∷ xs) = try pass x (try refill x (expand xs))

  scan : List Station → List State → List State
  scan [] xs = xs
  scan (station s d ∷ route) xs = scan route (Pruning.thinlist (Move.expand s d xs))

  -- Starting with one unit, the only way across the two legs is to
  -- take two units at the first station. The second has no supply.
  -- Only one stop is needed; refilling there is dominated by passing.
example : Search.scan 3 (station 2 2 ∷ station 0 1 ∷ []) (at 0 1 ∷ []) ≡ at 1 0 ∷ []
example = refl
