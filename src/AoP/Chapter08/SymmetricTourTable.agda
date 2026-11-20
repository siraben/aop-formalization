{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.SymmetricTourTable where

open import AoP.Common.Prelude
open import AoP.Chapter08.Bitonic using (module Tours)
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter08.SymmetricTour using (module Law)
open import AoP.Chapter08.BitonicTable using (module DP)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 8.26. Keep only the outward orientation of each endpoint
-- pair in the dynamic-programming row. To use the other orientation,
-- reverse the stored route; symmetry leaves the cached price unchanged.
module Table {City : Set} (edge : City → City → Nat) (sym : ∀ a b → edge a b ≡ edge b a) (end : City) where
  open Tours edge
  open Law edge sym using (flip; reverse-cost)
  open DP edge end using (Cell; cell; update; base)
  private
    back : ∀ {a b : Nat} → a ≡ b → b ≡ a
    back refl = refl

  mirror : ∀ {u v xs} → Cell u v xs → Cell v u xs
  mirror {u} {v} (cell p price value least) = cell (flip p) price (reverse-cost u v end p ∙ value) optimal
    where optimal : ∀ q → price ≤ cost v u end q
          optimal q rewrite back (reverse-cost v u end q) = least (flip q)

  data Row (u : City) (xs : List City) : List City → Set where
    nil : Row u xs []
    cons : ∀ {v vs} → Cell u v xs → Row u xs vs → Row u xs (v ∷ vs)

  close-row : ∀ u vs → Row u [] vs
  close-row u [] = nil
  close-row u (v ∷ vs) = cons (base u v) (close-row u vs)

  retreat : ∀ u x {xs vs} → Cell u x xs → Row x xs vs → Row u (x ∷ xs) vs
  retreat u x shared nil = nil
  retreat u x shared (cons c cs) = cons (update u _ x c shared) (retreat u x shared cs)

  table : ∀ u xs vs → Row u xs vs
  table u [] vs = close-row u vs
  table u (x ∷ xs) vs with table x xs (u ∷ vs)
  ... | cons xu rest = retreat u x (mirror xu) rest

  solve-table : ∀ s xs → Cell s s xs
  solve-table s xs with table s xs (s ∷ [])
  ... | cons winner nil = winner
