{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MonotoneConstructor where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations

-- Exercise 7.34 for initial algebras of containers. Each constructor
-- has a shape and one recursive argument per position. Its relational
-- lifting compares matching shapes positionwise. If constructing a
-- layer preserves R, self-comparison follows by induction on the tree.
module Container (Shape : Set) (Pos : Shape → Set) where
  data Tree : Set where
    node : (s : Shape) → (Pos s → Tree) → Tree

  module Law (R : Tree ← Tree)
             (mono : ∀ s (f g : Pos s → Tree) → (∀ i → R (f i) (g i)) → R (node s f) (node s g)) where
    reflexive : ∀ t → R t t
    reflexive (node s f) = mono s f f (λ i → reflexive (f i))
