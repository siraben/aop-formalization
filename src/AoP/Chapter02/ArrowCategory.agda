{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ArrowCategory where

open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)

infixr 4 _×_
_×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A × B = Σ A (λ _ → B)
open import AoP.Chapter02.Categories
open import AoP.Chapter02.Cancellation using (module Laws′)

-- Exercise 2.8. An object is a single arrow. A map between objects
-- changes its two endpoints compatibly. Composition pastes two squares
-- horizontally, leaving the middle vertical arrow inside the diagram.
module Arrows {o h e} (C : Category o h e) where
  open Category C
  record Arrow : Set (o ⊔ h) where
    constructor arrow
    field source target : Obj
          edge : Hom source target
  open Arrow
  record Square (f g : Arrow) : Set (h ⊔ e) where
    constructor box
    field top : Hom (source f) (source g)
          bottom : Hom (target f) (target g)
          commutes : edge g ∘ top ≈ bottom ∘ edge f
  open Square

  paste : ∀ {f g k} → Square g k → Square f g → Square f k
  paste {f} {g} {k} b a = box (top b ∘ top a) (bottom b ∘ bottom a) law
    where
    law = transitive (symmetric (assoc (edge k) (top b) (top a)))
          (transitive (compose-cong (commutes b) reflexive)
          (transitive (assoc (bottom b) (edge g) (top a))
          (transitive (compose-cong reflexive (commutes a))
                      (symmetric (assoc (bottom b) (bottom a) (edge f))))))

  Arr : Category _ _ _
  Category.Obj Arr = Arrow
  Category.Hom Arr = Square
  Category._≈_ Arr a b = (top a ≈ top b) × (bottom a ≈ bottom b)
  Category.identity Arr {f} = box identity identity (transitive (unitʳ (edge f)) (symmetric (unitˡ (edge f))))
  Category._∘_ Arr = paste
  Category.reflexive Arr = reflexive , reflexive
  Category.symmetric Arr (p , q) = symmetric p , symmetric q
  Category.transitive Arr (a , b) (c , d) = transitive a c , transitive b d
  Category.compose-cong Arr (a , b) (c , d) = compose-cong a c , compose-cong b d
  Category.unitˡ Arr f = unitˡ (top f) , unitˡ (bottom f)
  Category.unitʳ Arr f = unitʳ (top f) , unitʳ (bottom f)
  Category.assoc Arr k g f = assoc (top k) (top g) (top f) , assoc (bottom k) (bottom g) (bottom f)

  pointwise-monic : ∀ {f g} (s : Square f g) → Laws′.Monic C (top s) → Laws′.Monic C (bottom s) → Laws′.Monic Arr s
  pointwise-monic s mt mb a b (eq₁ , eq₂) = mt (top a) (top b) eq₁ , mb (bottom a) (bottom b) eq₂
