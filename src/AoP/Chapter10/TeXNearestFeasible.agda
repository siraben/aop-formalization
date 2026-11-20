{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXNearestFeasible where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; s≤; z≤; chain; weaken; rid)
open import AoP.Chapter10.TeXNearestNeighbours using (err; module Choose)
open import AoP.Chapter10.TeXNearestClamp using (module Clamp)
open import AoP.Chapter10.TeXNumeratorBounds using (module Range)
open import AoP.Chapter10.StrictUpperQuotient using (choose; cell)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- The interval uses the decoder's scale (131072 for TeX); the error
-- uses the target's scale (65536). Keep the two parameters distinct.
module Select (interval-divisor error-divisor L h cap target : Nat) where
  module R = Range interval-divisor L h cap
  w = suc error-divisor
  a = choose error-divisor target
  bracket = cell error-divisor target
  module N = Choose w target a (fst bracket) (chain (weaken (rid target)) (snd bracket))
  cost = λ i → err (i * w) target
  -- Any already certified shortest output witnesses nonemptiness at
  -- the chosen width. The algorithm does not enumerate its rivals.
  solve : ∀ base → R.Exactly base → Σ Nat (λ i → R.Exactly i × (∀ j → R.Exactly j → cost i ≤ cost j))
  solve base witness = finish (C.clamp (fst N.winner) (snd N.winner))
    where
    limits = R.project base witness
    module C = Clamp w target (R.ceil L) R.hi (chain (fst limits) (snd limits))
    finish : Σ Nat C.Best → Σ Nat (λ i → R.Exactly i × (∀ j → R.Exactly j → cost i ≤ cost j))
    finish (i , ((lo , hi) , best)) = i , (R.restore i lo hi , λ j ok → best j (R.project j ok))
