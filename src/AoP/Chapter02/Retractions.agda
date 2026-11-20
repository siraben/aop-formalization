{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.Retractions where

open import AoP.Chapter02.Categories

-- §2.1 exercises 2.1 and 2.3. To identify a purported right unit,
-- apply its defining equation to identity itself. To lift an arrow f
-- through a retraction, first follow f by the chosen section. The dual
-- extends an arrow from the domain of the section along that section.
module Laws {o h e} (C : Category o h e) where
  open Category C

  unique-id : ∀ {A} (u : Hom A A) → (∀ {B} (f : Hom A B) → f ∘ u ≈ f) → u ≈ identity
  unique-id u law = transitive (symmetric (unitˡ u)) (law identity)

  module Split {A B} (r : Hom B A) (s : Hom A B) (split : r ∘ s ≈ identity) where
    lift : ∀ {X} (f : Hom X A) → r ∘ (s ∘ f) ≈ f
    lift f = transitive (symmetric (assoc r s f))
             (transitive (compose-cong split (reflexive {f = f})) (unitˡ f))

    extend : ∀ {X} (f : Hom A X) → (f ∘ r) ∘ s ≈ f
    extend f = transitive (assoc f r s)
               (transitive (compose-cong (reflexive {f = f}) split) (unitʳ f))
