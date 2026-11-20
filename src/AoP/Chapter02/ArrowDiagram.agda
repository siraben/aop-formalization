{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ArrowDiagram where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Transformations using (Natural)
open import AoP.Chapter02.WalkingArrow
open import AoP.Chapter02.ArrowCategory using (module Arrows)
open import AoP.Chapter02.DiagramEvaluation using (module Evaluate)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)

-- Exercise 2.19, reverse direction. Send an arrow to its canonical
-- walking-arrow diagram and a commuting square to its two components.
-- The functor laws are componentwise: endpoints of pasted squares are
-- precisely the composites of the corresponding endpoint maps.
module Canonical {o h e} (C : Category o h e) where
  open Category C using (reflexive)
  open Arrows C
  open Arrow
  open Square
  open Evaluate C
  open Functor using (F₀; F₁)
  open Natural using (η)

  diagram-of : Arrow → Category.Obj Diag
  diagram-of a = Diagrams.diagram C (edge a)

  components : ∀ {a b} → Square a b → Natural (diagram-of a) (diagram-of b)
  components {a} {b} s = M.write (M.box (top s) (bottom s) (commutes s))
    where module M = Diagrams.Maps C (diagram-of a) (diagram-of b)

  canonical : Functor Arr Diag
  F₀ canonical = diagram-of
  F₁ canonical = components
  Functor.resp canonical (p , q) src = p
  Functor.resp canonical (p , q) dst = q
  Functor.identity canonical src = reflexive
  Functor.identity canonical dst = reflexive
  Functor.composition canonical g f src = reflexive
  Functor.composition canonical g f dst = reflexive

  object-round : ∀ a → F₀ evaluate (F₀ canonical a) ≡ a
  object-round (arrow _ _ _) = refl

  square-round : ∀ {a b} (s : Square a b) → Category._≈_ Arr (F₁ evaluate (F₁ canonical s)) s
  square-round s = reflexive , reflexive
