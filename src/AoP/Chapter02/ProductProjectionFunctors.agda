{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ProductProjectionFunctors where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.ProductCategory using (module Product)
open import Agda.Builtin.Sigma using (fst; snd; _,_)

-- §2.5. A projection forgets one coordinate of both objects and arrows.
-- Identity and composition survive because the product category computes
-- them separately in each coordinate.
module Projections {o h e o′ h′ e′} (A : Category o h e) (B : Category o′ h′ e′) where
  module P = Product A B
  left : Functor P.prod A
  Functor.F₀ left = fst
  Functor.F₁ left = fst
  Functor.resp left = fst
  Functor.identity left = Category.reflexive A
  Functor.composition left g f = Category.reflexive A
  right : Functor P.prod B
  Functor.F₀ right = snd
  Functor.F₁ right = snd
  Functor.resp right = snd
  Functor.identity right = Category.reflexive B
  Functor.composition right g f = Category.reflexive B

  -- Conversely two interpretations of the same source can run side by
  -- side. Projecting the resulting arrow recovers either interpretation.
  module Together {o″ h″ e″} {C : Category o″ h″ e″} (F : Functor C A) (G : Functor C B) where
    pair : Functor C P.prod
    Functor.F₀ pair x = Functor.F₀ F x , Functor.F₀ G x
    Functor.F₁ pair f = Functor.F₁ F f , Functor.F₁ G f
    Functor.resp pair p = Functor.resp F p , Functor.resp G p
    Functor.identity pair = Functor.identity F , Functor.identity G
    Functor.composition pair g f = Functor.composition F g f , Functor.composition G g f

    recover-left : ∀ {X Y} (f : Category.Hom C X Y) → Category._≈_ A (Functor.F₁ left (Functor.F₁ pair f)) (Functor.F₁ F f)
    recover-left f = Category.reflexive A
    recover-right : ∀ {X Y} (f : Category.Hom C X Y) → Category._≈_ B (Functor.F₁ right (Functor.F₁ pair f)) (Functor.F₁ G f)
    recover-right f = Category.reflexive B
