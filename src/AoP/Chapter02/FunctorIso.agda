{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.FunctorIso where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import Agda.Primitive using (_⊔_)

-- Exercise 2.9. Given an inverse, map it with the same functor. Each
-- round trip follows from preservation of composition, the original
-- inverse law, and preservation of identity, in that order.
module Arrows {o h e} (C : Category o h e) where
  open Category C
  record Inverse {A B} (f : Hom A B) : Set (h ⊔ e) where
    constructor inverse
    field back : Hom B A
          left : back ∘ f ≈ identity
          right : f ∘ back ≈ identity

module Preservation {o h e o′ h′ e′} {C : Category o h e} {D : Category o′ h′ e′}
                    (F : Functor C D) where
  private module C = Category C
  private module D = Category D
  open Functor F

  round : ∀ {A B} (f : C.Hom A B) (g : C.Hom B A) → g C.∘ f C.≈ C.identity →
          F₁ g D.∘ F₁ f D.≈ D.identity
  round f g law = D.transitive (D.symmetric (composition g f))
                  (D.transitive (resp law) identity)

  preserve : ∀ {A B} (f : C.Hom A B) → Arrows.Inverse C f → Arrows.Inverse D (F₁ f)
  preserve f (Arrows.inverse g left right) = Arrows.inverse (F₁ g) (round f g left) (round g f right)
