{-# OPTIONS --safe --without-K #-}
module AoP.ConstantArrow where

open import AoP.Categories
open import AoP.UniversalObjects using (module Universal)
open import Agda.Primitive using (_⊔_)

-- Exercise 2.20. Regard an element as an arrow out of the terminal
-- object. Every map into that object forgets its input. To identify the
-- value of a constant c on B, choose an element b of B and evaluate c
-- there. This last step is the reason for the inhabitance hypothesis.
module Elements {o h e} (C : Category o h e) {T} (terminal : Universal.Terminal C T) where
  open Category C
  open Universal.Terminal terminal

  Constant : ∀ {A B} → Hom B A → Set (o ⊔ h ⊔ e)
  Constant {B = B} c = ∀ {X} (f g : Hom X B) → c ∘ f ≈ c ∘ g

  element-constant : ∀ {A} (a : Hom T A) → Constant a
  element-constant a f g = compose-cong (reflexive {f = a}) (transitive (unique f) (symmetric (unique g)))

  factor : ∀ {A B} (c : Hom B A) → Constant c → (b : Hom T B) → c ≈ (c ∘ b) ∘ enter B
  factor {B = B} c const b = transitive (symmetric (unitʳ c))
    (transitive (const identity (b ∘ enter B)) (symmetric (assoc c b (enter B))))
