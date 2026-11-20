{-# OPTIONS --safe --without-K #-}
module AoP.FiveMoveEntry where

open import AoP.Prelude
open import AoP.FiveMoveCylinder using (module Grid)
open import AoP.FiniteMinimum using (module Search)
open import AoP.Subsequences using (_∈_; here)
open import AoP.Polynomial using (inl)
open import AoP.NatOrder using (_≤_; chain)

-- Exercise 7.46 with a free entry point: compare the optimal fixed-row
-- routes on a nonempty rim. The winner must come from that rim, and
-- beats every route starting from any of its listed rows.
module Rim (Row : Set) (up down : Row → Row) (open Grid Row up down)
           (c : Column) (cs : List Column) where
  route : Row → Path cs
  route r = fst (solve c r cs)
  price = λ r → cost c r (route r)
  module M = Search (λ (_ : Row) → ⊤) (λ _ → inl tt) price
  record Result (rows : List Row) : Set where
    constructor win
    field entry : Row
          on-rim : entry ∈ rows
          least : ∀ r → r ∈ rows → (q : Path cs) → price entry ≤ cost c r q
  choose : ∀ r rs → Result (r ∷ rs)
  choose r rs with M.scan (r ∷ rs)
  ... | M.none no = M.absurd (no r here tt)
  ... | M.best s valid _ bound = win s valid λ t mem q → chain (bound t mem tt) (snd (solve c t cs) q)
