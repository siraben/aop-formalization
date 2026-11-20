{-# OPTIONS --safe --without-K #-}
module AoP.CylinderTableWinner where

open import AoP.Prelude
open import AoP.CylinderFiniteRim
open import AoP.Cylinder using (module Grid)
open import AoP.CylinderCachedColumn using (module Table)
open import AoP.NatOrder using (_≤_; compare; rid; chain)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- The final reduction scans the first column: its entries already
-- include all continuation costs. With h positive rows this takes
-- h−1 score comparisons, independent of the lengths of the routes.
min-row : ∀ n (f : Row (suc n) → Nat) → Σ (Row (suc n)) λ r → ∀ s → f r ≤ f s
min-row zero f = top , λ { top → rid _ ; (below ()) }
min-row (suc n) f with min-row n (λ i → f (below i))
... | i , lb with compare (f top) (f (below i))
...   | inl le = top , λ { top → rid _ ; (below j) → chain le (lb j) }
...   | inr ge = below i , λ { top → ge ; (below j) → lb j }

module Cylinder (n : Nat) where
  open Grid (Row (suc n)) up down using (Column; Path; cost)
  open Table (Row (suc n)) up down using (Cell)
  open Solve n using (solve)
  record Winner (c : Column) (cs : List Column) : Set where
    constructor win
    field start : Row (suc n)
          selected : Cell c start cs
          global : ∀ r (p : Path cs) → Cell.score selected ≤ cost c r p

  optimum : ∀ c cs → Winner c cs
  optimum c cs = finish (min-row n (λ i → Cell.score (entry i)))
    where
      entry = get (λ r → Cell c r cs) (solve c cs)
      finish : (Σ (Row (suc n)) λ i → ∀ j → Cell.score (entry i) ≤ Cell.score (entry j)) → Winner c cs
      finish (i , lower) = win i (entry i) (λ r p → chain (lower r) (Cell.least (entry r) p))
