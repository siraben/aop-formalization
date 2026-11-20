{-# OPTIONS --safe --without-K #-}
module AoP.SimpleZigzag where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (Id)
open import AoP.ModularRefinement using (zigzag)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 4.15. A simple relation returns at most one output per
-- input. The two outputs joined at the first bend of a zigzag must
-- therefore coincide, leaving just the final edge.
module Law {A B : Set} (S : B ← A) (simple : S ∘ S ˘ ⊆ Id) where
  expand = zigzag S

  contract : S ∘ S ˘ ∘ S ⊆ S
  contract (a , s , b , t , u) with simple (a , s , t)
  ... | refl = u

-- From a singleton allow either Boolean output. Every zigzag still
-- contracts because all possible endpoint pairs are already edges.
-- Simplicity would identify true and false.
choice : Bool ← ⊤
choice _ _ = ⊤

contracts : choice ∘ choice ˘ ∘ choice ⊆ choice
contracts _ = tt

not-simple : (choice ∘ choice ˘ ⊆ Id) → ⊥
not-simple law with law {true} {false} (tt , tt , tt)
... | ()
