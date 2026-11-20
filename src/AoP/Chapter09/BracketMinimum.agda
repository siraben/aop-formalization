{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.BracketMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin)
open import AoP.Chapter09.BracketSpine using (leaves)
open import AoP.Chapter09.BracketEnumeration using (enumerate; complete; sound)
open import AoP.Common.FiniteMinimum using (module Search)
open import AoP.Chapter02.Polynomial using (inl)
open import AoP.Common.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat)

-- §9.3. Among trees spelling the given operands, select a least-cost
-- one. A single operand needs no binary operation. For longer inputs,
-- right association supplies an initial feasibility witness, irrespective
-- of cost. The exhaustive solver accepts any natural-valued cost model.
module Solve {A : Set} (cost : Tree A → Nat) where
  module S = Search (λ (_ : Tree A) → ⊤) (λ _ → inl tt) cost

  witness : (a : A) (xs : List A) → Σ (Tree A) λ t → leaves t ≡ a ∷ xs
  witness a [] = tip a , refl
  witness a (b ∷ xs) with witness b xs
  ... | t , eq = bin (tip a) t , cong (a ∷_) eq

  record Best (xs : List A) : Set where
    constructor best
    field
      tree : Tree A
      operands : leaves tree ≡ xs
      optimal : ∀ u → leaves u ≡ xs → cost tree ≤ cost u

  solve : ∀ a xs → Best (a ∷ xs)
  solve a xs with S.scan (enumerate (a ∷ xs))
  ... | S.best t m _ least = best t (sound _ m) (λ u eq → least u (complete _ u eq) tt)
  ... | S.none no with witness a xs
  ...   | t , eq with no t (complete _ t eq) tt
  ...     | ()
