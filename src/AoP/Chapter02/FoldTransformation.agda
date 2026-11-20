{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.FoldTransformation where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.FunctorCategory using (module Construction)
open import AoP.Chapter02.Transformations using (Natural)
open import AoP.Chapter02.Whiskering using (module Through)
open import AoP.Chapter02.InitialTypeFunctor using (module Derive)
open import AoP.Chapter02.ParametricFoldSquare using (module Square)

-- Exercise 2.39. Specialize each layer to the parameter G X and give
-- H X an algebra for it. If these operations commute with every arrow
-- of the index category, their folds form a natural transformation.
module Family {o h e o′ h′ e′ o″ h″ e″} (D : Category o h e)
  (P : Category o′ h′ e′) (C : Category o″ h″ e″)
  (layers : Functor P (Construction.cat C C)) where
  open Category C
  open Derive P C layers
  module Result I i (G : Functor D P) (H : Functor D C) where
    open Build I i
    module G = Functor G
    module H = Functor H
    module Consumer (a : ∀ X → Hom (Functor.F₀ (L.F₀ (G.F₀ X)) (H.F₀ X)) (H.F₀ X))
      (law : ∀ {X Y} (f : Category.Hom D X Y) → H.F₁ f ∘ a X ≈
        (a Y ∘ Natural.η (L.F₁ (G.F₁ f)) (H.F₀ Y)) ∘ Functor.F₁ (L.F₀ (G.F₀ X)) (H.F₁ f)) where
      folds : Natural (Through.compose G datatype) H
      Natural.η folds X = F.fold (G.F₀ X) (Alg.alg _ (a X))
      Natural.square folds {X} {Y} f = Square.Proof.commute C (L.F₁ (G.F₁ f)) (i _) (i _)
        (Alg.alg _ (a X)) (Alg.alg _ (a Y)) (H.F₁ f) (law f)
