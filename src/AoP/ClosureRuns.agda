{-# OPTIONS --safe --without-K #-}
module AoP.ClosureRuns where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Closure using (module Paths)
open import AoP.Complement using (_⊔_)
open import AoP.Polynomial using (inl; inr)

-- Exercise 6.36, path calculation. Split a path at every S edge.
-- Between separators only R is used. Consecutive S edges therefore
-- produce empty R runs, as does a separator at either endpoint.
module Runs {A : Set} (R S : A ← A) where
  module U = Paths (R ⊔ S)
  module Pure = Paths R
  module Blocks = Paths (S ∘ Pure.Star)
  Normal = Pure.Star ∘ Blocks.Star

  split : U.Star ⊆ Normal
  split U.stop = _ , Pure.stop , Blocks.stop
  split (U.extend (inl r) p) with split p
  ... | a , tail , before = a , Pure.extend r tail , before
  split (U.extend (inr s) p) with split p
  ... | a , tail , before = _ , Pure.stop , Blocks.extend (_ , s , tail) before

  run : Pure.Star ∘ U.Star ⊆ U.Star
  run (_ , Pure.stop , p) = p
  run (_ , Pure.extend r tail , p) = U.extend (inl r) (run (_ , tail , p))

  blocks : Blocks.Star ⊆ U.Star
  blocks Blocks.stop = U.stop
  blocks (Blocks.extend (_ , s , tail) before) = U.extend (inr s) (run (_ , tail , blocks before))

  join : Normal ⊆ U.Star
  join (_ , tail , before) = run (_ , tail , blocks before)
