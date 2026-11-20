{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.Cancellation where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Retractions
open import Agda.Primitive using (_⊔_)

-- §2.1, exercises 2.4–2.5. A section cancels on the left because we
-- can apply its retraction. The dual calculation cancels a retraction
-- on the right. These arguments work with any category's arrow equality.
module Laws′ {o h e} (C : Category o h e) where
  open Category C
  Monic : ∀ {A B} → Hom A B → Set (o ⊔ h ⊔ e)
  Monic {A} f = ∀ {X} (a b : Hom X A) → f ∘ a ≈ f ∘ b → a ≈ b

  Epic : ∀ {A B} → Hom A B → Set (o ⊔ h ⊔ e)
  Epic {B = B} f = ∀ {X} (a b : Hom B X) → a ∘ f ≈ b ∘ f → a ≈ b

  module SplitPair {A B} (r : Hom B A) (s : Hom A B) (rs : r ∘ s ≈ identity) where
    open Laws.Split C r s rs
    section-monic : Monic s
    section-monic a b eq = transitive (symmetric (lift a))
      (transitive (compose-cong (reflexive {f = r}) eq) (lift b))

    retraction-epic : Epic r
    retraction-epic a b eq = transitive (symmetric (extend a))
      (transitive (compose-cong eq (reflexive {f = s})) (extend b))

  outside-epic : ∀ {A B D} (f : Hom B D) (g : Hom A B) → Epic (f ∘ g) → Epic f
  outside-epic f g cancel a b eq = cancel a b (transitive (symmetric (assoc a f g))
    (transitive (compose-cong eq (reflexive {f = g})) (assoc b f g)))

  inside-monic : ∀ {A B D} (f : Hom B D) (g : Hom A B) → Monic (f ∘ g) → Monic g
  inside-monic f g cancel a b eq = cancel a b (transitive (assoc f g a)
    (transitive (compose-cong (reflexive {f = f}) eq) (symmetric (assoc f g b))))
