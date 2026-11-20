{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.BusMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter08.BusReference using (module Plan; chosen)
open import AoP.Chapter08.BusWalking using (trips)
open import AoP.Chapter08.BusProfile using (Stops; sites)
open import AoP.Chapter08.BusProfileCost using (indices; cost; cost-bound)
open import AoP.Chapter08.BusFrontier using (module Generate)
open import AoP.Chapter08.BusFrontierCoverage using (module Law)
open import AoP.Chapter08.BusFrontierSound using (stops) renaming (module Law to Sound)
open import AoP.Chapter08.BusLayouts using (done)
open import AoP.Common.FiniteMinimum using (module Search)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_; chain)
open import AoP.Chapter02.Polynomial using (inl)
open import Agda.Builtin.Nat using (Nat; suc)

-- Return the same certificate as exhaustive search. Only the surviving
-- layouts enter the minimum scan. A cheaper competitor would have a
-- survivor no dearer still, contradicting minimality among survivors.
module Solve (bs : List (Nat × Nat)) where
  js = indices 0 bs
  score : Stops → Nat
  score w = cost w 0 bs
  module M = Search (λ (_ : Stops) → ⊤) (λ _ → inl tt) score
  solve : ∀ k → Plan.Answer bs k
  solve 0 = Plan.impossible λ { [] (_ , ()) ; (_ ∷ _) (() , _) }
  solve (suc k) with M.scan (Generate.build js 0 (len bs) k)
  ... | M.none no = Plan.impossible λ where
    [] (_ , ())
    (y ∷ ys) (legal , _) → let w , m , _ = Law.cover js legal in no w m tt
  ... | M.best (sites x xs) m _ least = Plan.best (x ∷ xs) (Sound.valid js 0 (len bs) k m , tt) λ where
    [] (_ , ())
    (y ∷ ys) (legal , _) → let w , mem , p = Law.cover js legal in
      chain (least w mem tt) (cost-bound 0 bs w (sites y ys) p)

example : chosen (Solve.solve trips 2) ≡ 0 ∷ 2 ∷ []
example = refl
