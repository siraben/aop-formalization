{-# OPTIONS --safe --without-K #-}
module AoP.UniversalObjects where

open import Agda.Primitive using (_⊔_)
open import AoP.Categories
open import AoP.Prelude
open import AoP.Complement using (⊥)

-- §2.4. Describe an object by how programs may enter or leave it,
-- rather than by inspecting its representation. An initial object has
-- exactly one map to each target; a terminal object has exactly one
-- map from each source. Uniqueness is the category's arrow equivalence.
module Universal {o h e} (C : Category o h e) where
  open Category C
  record Initial (I : Obj) : Set (o ⊔ h ⊔ e) where
    field
      leave : ∀ A → Hom I A
      unique : ∀ {A} (f : Hom I A) → f ≈ leave A
    fusion : ∀ {A B} (f : Hom A B) → f ∘ leave A ≈ leave B
    fusion f = unique _

  record Terminal (T : Obj) : Set (o ⊔ h ⊔ e) where
    field
      enter : ∀ A → Hom A T
      unique : ∀ {A} (f : Hom A T) → f ≈ enter A
    fusion : ∀ {A B} (f : Hom A B) → enter B ∘ f ≈ enter A
    fusion f = unique _

  -- Two terminal objects are interchangeable up to isomorphism: going
  -- across and back is an endomorphism of a terminal object, hence it
  -- equals identity by the same uniqueness law. Swap t and u for the
  -- other half of the isomorphism.
  round-trip : ∀ {T U} (t : Terminal T) (u : Terminal U) →
               Terminal.enter t U ∘ Terminal.enter u T ≈ identity
  round-trip t u = transitive (Terminal.unique t _) (symmetric (Terminal.unique t identity))

open Universal Fun

empty-initial : Initial ⊥
Initial.leave empty-initial A ()
Initial.unique empty-initial f ()

unit-terminal : Terminal ⊤
Terminal.enter unit-terminal A a = tt
Terminal.unique unit-terminal f a = refl
