{-# OPTIONS --safe --without-K #-}
module AoP.OppositeComposition where

open import AoP.Prelude
open import AoP.Relations
open import AoP.ResidualConnections using (module Connections)

-- Exercise 4.37. Right composition changes the input end of an edge;
-- left composition changes the output end. For the proposed maps to
-- have opposite types, R and S must be endorelations at these ends.
-- The proposed adjunction says X ∘ R ⊆ Y iff X ⊆ S ∘ Y for all X,Y.
-- Equivalently the round trips expand X and contract Y, respectively.
module Test {A B : Set} (R : A ← A) (S : B ← B) where
  open Connections (_∘ R) (S ∘_) using (Connection)
  open Connection
  Unit = (X : B ← A) → X ⊆ S ∘ (X ∘ R)
  Counit = (Y : B ← A) → (S ∘ Y) ∘ R ⊆ Y

  unit-law : Connection → Unit
  unit-law adj X = up adj X (X ∘ R) (λ p → p)
  counit-law : Connection → Counit
  counit-law adj Y = down adj (S ∘ Y) Y (λ p → p)

  sufficient : Unit → Counit → Connection
  up (sufficient unit counit) X Y incl x with unit X x
  ... | b , s , xr = b , s , incl xr
  down (sufficient unit counit) X Y incl (a , x , r) = counit Y (a , incl x , r)
