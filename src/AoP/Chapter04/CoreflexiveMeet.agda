{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.CoreflexiveMeet where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id)
private variable A : Set

-- Exercises 4.8–9 in Rel. A coreflexive relation is a test: a
-- successful step keeps its input unchanged. In a composite of tests
-- the intermediate state must therefore equal both endpoints. This
-- turns sequential tests into conjunction on a single state.
module Tests (P Q : A ← A) (p-id : P ⊆ Id) (q-id : Q ⊆ Id) where
  sequential : P ∘ Q ⊆ P ⊓ Q
  sequential (b , p , q) with p-id p | q-id q
  ... | refl | refl = p , q

  together : P ⊓ Q ⊆ P ∘ Q
  together (p , q) with p-id p
  ... | refl = _ , p , q

transitive : (P : A ← A) → P ⊆ Id → P ∘ P ⊆ P
transitive P core witness = fst (Tests.sequential P P core core witness)
