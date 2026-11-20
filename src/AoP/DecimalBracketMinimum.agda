{-# OPTIONS --safe --without-K #-}
module AoP.DecimalBracketMinimum where

open import AoP.Prelude
open import AoP.BracketMinimum using (module Solve)
open import AoP.DecimalBracketCost using (module Sum; module Product)
open import AoP.Trees using (tip; bin)

-- Exhaustive reference programs for the two decimal cost models.
-- Best.operands preserves the input order. Best.optimal compares the
-- returned cost with every tree spelling that same operand list.
module Add = Solve Sum.cost
module Multiply = Solve Product.cost

-- Four operands: the middle pair can be reduced before either outside
-- operand. All parentheses are chosen by the reference search.
addition : Sum.cost (Add.Best.tree (Add.solve 9 (1 ∷ 1 ∷ 1 ∷ []))) ≡ 3
addition = refl
multiplication : Product.cost (Multiply.Best.tree (Multiply.solve 9 (2 ∷ 1 ∷ 1 ∷ []))) ≡ 3
multiplication = refl
