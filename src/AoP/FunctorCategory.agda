{-# OPTIONS --safe --without-K #-}
module AoP.FunctorCategory where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.Transformations using (Natural; module Vertical)

-- Exercise 2.19. Functors C → D are objects; transformations between
-- them are arrows. Compare transformations at each object of C using
-- D's arrow equality. Thus the proofs of naturality need never be
-- compared, and the categorical laws reduce to laws in D.
module Construction {o h e o′ h′ e′} (C : Category o h e) (D : Category o′ h′ e′) where
  private module D = Category D
  open Natural using (η; square)

  unit : (F : Functor C D) → Natural F F
  η (unit F) X = D.identity
  square (unit F) f = D.transitive (D.unitʳ _) (D.symmetric (D.unitˡ _))

  cat : Category _ _ _
  Category.Obj cat = Functor C D
  Category.Hom cat = Natural
  Category._≈_ cat α β = ∀ X → η α X D.≈ η β X
  Category.identity cat = unit _
  Category._∘_ cat β α = Vertical.composite α β
  Category.reflexive cat X = D.reflexive
  Category.symmetric cat law X = D.symmetric (law X)
  Category.transitive cat ab bc X = D.transitive (ab X) (bc X)
  Category.compose-cong cat eq₁ eq₂ X = D.compose-cong (eq₁ X) (eq₂ X)
  Category.unitˡ cat α X = D.unitˡ (η α X)
  Category.unitʳ cat α X = D.unitʳ (η α X)
  Category.assoc cat γ β α X = D.assoc (η γ X) (η β X) (η α X)
