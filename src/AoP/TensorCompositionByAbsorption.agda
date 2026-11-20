{-# OPTIONS --safe --without-K #-}
module AoP.TensorCompositionByAbsorption where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (graph)
open import AoP.RelationalProducts using (_⊗_)
open import AoP.RelationalPairing using (pair; branches)
open import AoP.PairAbsorptionCalculation using (module Relation)

-- §5.2. Derive the composition law for × from pairing absorption.
-- Expand the inner product with the two projections. After absorption,
-- each branch still contains its projection; evaluate these last.
module Derive {A B C D E F : Set} (U : B ← A) (V : D ← C) (R : E ← B) (S : F ← D) where
  X : B ← (A × C)
  X = U ∘ graph fst
  Y : D ← (A × C)
  Y = V ∘ graph snd
  expand : U ⊗ V ⊆ pair X Y
  expand (u , v) = (_ , u , refl) , (_ , v , refl)
  pack : pair X Y ⊆ U ⊗ V
  pack ((_ , u , refl) , (_ , v , refl)) = u , v
  collect : pair (R ∘ X) (S ∘ Y) ⊆ (R ∘ U) ⊗ (S ∘ V)
  collect ((b , r , _ , u , refl) , (d , s , _ , v , refl)) = (b , r , u) , (d , s , v)
  expose : (R ∘ U) ⊗ (S ∘ V) ⊆ pair (R ∘ X) (S ∘ Y)
  expose ((b , r , u) , (d , s , v)) = (b , r , _ , u , refl) , (d , s , _ , v , refl)
  forward : (R ⊗ S) ∘ (U ⊗ V) ⊆ (R ∘ U) ⊗ (S ∘ V)
  forward (mid , rs , uv) = collect (branches R S X Y (mid , rs , expand uv))
  backward : (R ∘ U) ⊗ (S ∘ V) ⊆ (R ⊗ S) ∘ (U ⊗ V)
  backward p with Relation.absorb R S X Y (expose p)
  ... | mid , rs , xy = mid , rs , pack xy
