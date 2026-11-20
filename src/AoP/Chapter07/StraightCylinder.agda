{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.StraightCylinder where

open import AoP.Common.Prelude
open import AoP.Chapter07.Cylinder using (module Grid)
open import Agda.Builtin.Nat using (Nat; _+_)

-- Exercise 7.47. With the singleton move {r}, the chosen entry row
-- determines the entire path. Sum its cell costs across the columns;
-- only the choice among entry rows remains an optimization problem.
module Law (Row : Set) (up down : Row → Row) where
  open Grid Row up down
  straight : (cs : List Column) → Path cs
  straight [] = exit
  straight (_ ∷ cs) = stay (straight cs)
  data OnlyStay : ∀ {cs} → Path cs → Set where
    end : OnlyStay exit
    next : ∀ {c cs} {p : Path cs} → OnlyStay p → OnlyStay (stay {c} p)

  valid : ∀ cs → OnlyStay (straight cs)
  valid [] = end
  valid (_ ∷ cs) = next (valid cs)
  forced : ∀ {cs} {p : Path cs} → OnlyStay p → p ≡ straight cs
  forced end = refl
  forced (next v) = cong stay (forced v)

  row-sum : Column → Row → List Column → Nat
  row-sum c r [] = c r
  row-sum c r (d ∷ ds) = c r + row-sum d r ds
  value : ∀ c r cs → cost c r (straight cs) ≡ row-sum c r cs
  value c r [] = refl
  value c r (d ∷ ds) = cong (c r +_) (value d r ds)
