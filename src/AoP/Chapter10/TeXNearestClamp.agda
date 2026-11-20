{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXNearestClamp where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; rid; chain; compare)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter10.TeXNearestNeighbours using (err; left; right)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; _*_)

-- Restrict nearest rounding to any inhabited closed interval of
-- integer numerators. Depending on the position of the target, moving
-- to an endpoint improves on the unrestricted winner, or the endpoint
-- is already closer than every feasible rival on the same side.
module Clamp (w t l h : Nat) (bounds : l ≤ h) where
  cost = λ i → err (i * w) t
  Feasible = λ i → (l ≤ i) × (i ≤ h)
  Best = λ i → Feasible i × (∀ j → Feasible j → cost i ≤ cost j)
  raise : ∀ i → i ≤ l → (∀ j → cost i ≤ cost j) → Best l
  raise i small opt with compare (l * w) t
  ... | inl le = (rid l , bounds) , λ j _ → chain (left _ _ t (Arithmetic.scale w small) le) (opt j)
  ... | inr ge = (rid l , bounds) , λ j ok → right t _ _ ge (Arithmetic.scale w (fst ok))
  cap : ∀ i → h ≤ i → (∀ j → cost i ≤ cost j) → Best h
  cap i large opt with compare (h * w) t
  ... | inl le = (bounds , rid h) , λ j ok → left _ _ t (Arithmetic.scale w (snd ok)) le
  ... | inr ge = (bounds , rid h) , λ j _ → chain (right t _ _ ge (Arithmetic.scale w large)) (opt j)
  clamp : ∀ i → (∀ j → cost i ≤ cost j) → Σ Nat Best
  clamp i opt with compare l i | compare i h
  ... | inr small | _ = l , raise i small opt
  ... | inl _ | inr large = h , cap i large opt
  ... | inl lo | inl hi = i , ((lo , hi) , λ j _ → opt j)
