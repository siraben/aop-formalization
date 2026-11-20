{-# OPTIONS --safe --without-K #-}
module AoP.RelatorTests where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (Id)
open import AoP.CoreflexiveMeet using (module Tests)

-- Exercise 5.2. On tests, intersection is sequential composition.
-- Monotonicity and identity preservation ensure that lifted tests are
-- still tests. Composition preservation then transports their meet.
module Law {A B : Set} (F : (A ← A) → B ← B)
           (mono : ∀ X Y → X ⊆ Y → F X ⊆ F Y) (unit : F Id ⊆ Id)
           (split : ∀ X Y → F (X ∘ Y) ⊆ F X ∘ F Y)
           (join : ∀ X Y → F X ∘ F Y ⊆ F (X ∘ Y)) where
  test : ∀ X → X ⊆ Id → F X ⊆ Id
  test X core fx = unit (mono X Id core fx)

  module At (X Y : A ← A) (cx : X ⊆ Id) (cy : Y ⊆ Id) where
    module Source = Tests X Y cx cy
    module Target = Tests (F X) (F Y) (test X cx) (test Y cy)
    forward : F (X ⊓ Y) ⊆ F X ⊓ F Y
    forward p = Target.sequential (split X Y (mono (X ⊓ Y) (X ∘ Y) Source.together p))
    backward : F X ⊓ F Y ⊆ F (X ⊓ Y)
    backward p = mono (X ∘ Y) (X ⊓ Y) Source.sequential (join X Y (Target.together p))
