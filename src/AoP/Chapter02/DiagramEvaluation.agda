{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.DiagramEvaluation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Transformations using (Natural)
open import AoP.Chapter02.WalkingArrow
open import AoP.Chapter02.ArrowCategory using (module Arrows)
open import AoP.Chapter02.FunctorCategory using (module Construction)
open import Agda.Builtin.Sigma using (_,_)

-- §2.3, exercise 2.19. Evaluate a walking-arrow diagram on its one
-- generating arrow. A transformation evaluates to its endpoint maps;
-- naturality at go is exactly the proof that the square commutes.
module Evaluate {o h e} (C : Category o h e) where
  open Arrows C
  open Category C using (reflexive)
  open Natural using (η; square)
  open Functor using (F₀; F₁)
  Diag = Construction.cat Walking C

  evaluate : Functor Diag Arr
  F₀ evaluate F = arrow (F₀ F src) (F₀ F dst) (F₁ F go)
  F₁ evaluate α = box (η α src) (η α dst) (square α go)
  Functor.resp evaluate law = law src , law dst
  Functor.identity evaluate = reflexive , reflexive
  Functor.composition evaluate β α = reflexive , reflexive

  -- Every square lifts back to a transformation; comparing endpoint
  -- maps is also sufficient to compare the transformations on all objects.
  full : ∀ {F G : Functor Walking C} (b : Square (F₀ evaluate F) (F₀ evaluate G)) →
         Agda.Builtin.Sigma.Σ (Natural F G) λ α → Category._≈_ Arr (F₁ evaluate α) b
  full {F} {G} (box u v law) = M.write (M.box u v law) , reflexive , reflexive
    where module M = Diagrams.Maps C F G

  faithful : ∀ {F G : Functor Walking C} (α β : Natural F G) →
             Category._≈_ Arr (F₁ evaluate α) (F₁ evaluate β) → Category._≈_ Diag α β
  faithful α β (p , q) src = p
  faithful α β (p , q) dst = q

  -- Every arrow is obtained on the nose by evaluating its canonical
  -- walking-arrow diagram, so the object map is surjective as well.
  covers : (a : Arrow) → Agda.Builtin.Sigma.Σ (Functor Walking C) λ F → F₀ evaluate F ≡ a
  covers (arrow A B f) = Diagrams.diagram C f , refl
