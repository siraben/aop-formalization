{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.TourNext where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat)

-- Exercise 8.25. Store the common first city separately from each
-- nonempty leg tail. The next pair consists of the first cities on
-- the two tails. Adding a new common first city replaces the old
-- first city on one leg and preserves it as next on the other.
module Legs (City : Set) where
  record Tour : Set where
    constructor legs
    field first left right : City
          leftRest rightRest : List City
  open Tour
  next : Tour → City × City
  next t = left t , right t

  dropl dropr : City → Tour → Tour
  dropl a (legs b l r ls rs) = legs a l b ls (r ∷ rs)
  dropr a (legs b l r ls rs) = legs a b r (l ∷ ls) rs

  next-left : ∀ a t → next (dropl a t) ≡ (left t , first t)
  next-left a (legs b l r ls rs) = refl
  next-right : ∀ a t → next (dropr a t) ≡ (first t , right t)
  next-right a (legs b l r ls rs) = refl

module Example where
  open Legs Nat
  start = legs 2 3 3 [] []
  layer : (Nat × Nat) × (Nat × Nat)
  layer = next (dropl 1 start) , next (dropr 1 start)
  first-layer : layer ≡ ((3 , 2) , (2 , 3))
  first-layer = refl
