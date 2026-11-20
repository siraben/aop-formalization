{-# OPTIONS --safe --without-K #-}
module AoP.UnitRange where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (Id)
open import AoP.RangeRotation using (ran)
open import AoP.DomainPullback using (dom)

-- Exercise 4.26. A relation from the singleton describes a collection
-- of outputs. Projecting away its input loses no information: every
-- possible input is tt. Thus range both preserves and reflects order.
module Subsets {A : Set} (X Y : A ← ⊤) where
  preserve : X ⊆ Y → ran X ⊆ ran Y
  preserve incl (eq , tt , x) = eq , tt , incl x

  reflect : ran X ⊆ ran Y → X ⊆ Y
  reflect incl {b} {tt} x with incl {b} {b} (refl , tt , x)
  ... | _ , tt , y = y

-- Exercise 4.27. Compose with the universal relation to forget which
-- output S reached. Intersect with identity to obtain a test that
-- accepts precisely the inputs from which at least one edge leaves.
module Domain {A B : Set} (S : B ← A) where
  universal : A ← B
  universal _ _ = ⊤

  expand : dom S ⊆ Id ⊓ (universal ∘ S)
  expand (refl , b , s) = refl , b , tt , s

  collapse : Id ⊓ (universal ∘ S) ⊆ dom S
  collapse (refl , b , tt , s) = refl , b , s
