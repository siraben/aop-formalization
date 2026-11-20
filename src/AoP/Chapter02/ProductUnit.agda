{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ProductUnit where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.UniversalObjects using (module Universal)
open import AoP.Chapter02.FunctorIso using (module Arrows)

-- Exercise 2.26. At A × 1 the second projection carries no information:
-- every map into 1 agrees. Pairing the identity with the unique map to
-- 1 therefore recovers the inverse of the first projection.
module Unit {o h e} (C : Category o h e) where
  open Category C
  module For {T} (terminal : Universal.Terminal C T)
             (P : Obj → Obj) (π : ∀ A → Hom (P A) A) (τ : ∀ A → Hom (P A) T)
             (pair : ∀ {X A} → Hom X A → Hom X T → Hom X (P A))
             (project : ∀ {X A} (f : Hom X A) g → π A ∘ pair f g ≈ f)
             (ext : ∀ {X A} (f g : Hom X (P A)) → π A ∘ f ≈ π A ∘ g → τ A ∘ f ≈ τ A ∘ g → f ≈ g) where
    open Universal.Terminal terminal
    insert : ∀ A → Hom A (P A)
    insert A = pair identity (enter A)

    iso : ∀ A → Arrows.Inverse C (π A)
    iso A = Arrows.inverse (insert A) (ext _ _ observed (transitive (unique _) (symmetric (unique _)))) (project _ _)
      where
      observed : π A ∘ (insert A ∘ π A) ≈ π A ∘ identity
      observed = transitive (symmetric (assoc _ _ _))
        (transitive (compose-cong (project _ _) reflexive) (transitive (unitˡ _) (symmetric (unitʳ _))))

    map : ∀ {A B} → Hom A B → Hom (P A) (P B)
    map {A} f = pair (f ∘ π A) (τ A)

    -- The naturality square is the first projection law for the map
    -- between products. The other coordinate has no choice.
    natural : ∀ {A B} (f : Hom A B) → π B ∘ map f ≈ f ∘ π A
    natural f = project _ _
