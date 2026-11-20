{-# OPTIONS --safe --without-K #-}
module AoP.ImageUnionLaws where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.Transformations using (Natural)
open import AoP.ImageSingletonNaturality using (module Derive)
open import AoP.PowerTransposeTerminal using (module Slice)
open import AoP.ExistentialImageFunctor using (module Build)

-- §4.6. Flatten a family by taking the existential image of membership.
-- Singleton and union are arrows between power objects; the equalities
-- below compare arrows, without requiring equality of representations.
module Law {o h e o′ h′ e′} (C : Category o h e) (D : Category o′ h′ e′)
  (J : Functor C D) P mem where
  open Build C D J P mem
  private module C = Category C
  private module D = Category D
  private module J = Functor J
  module GivenLaws (laws : ∀ A → U.Laws A) where
    open Given laws
    open Derive.GivenLaws C D J P mem laws using (power; membership; singleton)
    private module Pow = Functor power
    η = Natural.η singleton
    μ : ∀ X → C.Hom (Pow.F₀ (Pow.F₀ X)) (Pow.F₀ X)
    μ X = E (mem (J.F₀ X))

    -- Take the union of a singleton family: absorption leaves the
    -- transpose of membership, which is identity by reflection.
    singleton-family : ∀ X → (μ X C.∘ η (Pow.F₀ X)) C.≈ C.identity
    singleton-family X = C.transitive (absorb _ _) (C.transitive (congruent (D.unitʳ _))
      (C.symmetric (U.Derived.reflection _ (laws _))))

    -- Take the union of the singleton images of a set. Combining the
    -- two images exposes membership after singleton, which cancels.
    singleton-elements : ∀ X → (μ X C.∘ Pow.F₁ (η X)) C.≈ C.identity
    singleton-elements X = C.transitive (C.symmetric (Functor.composition image _ _))
      (C.transitive (Functor.resp image (L.cancel _ _)) (Functor.identity image))

    -- Naturality of union for arbitrary relation arrows r: image of a
    -- flattened family equals flattening after taking the image of
    -- every member. Both sides are E applied to the membership square.
    union-square : ∀ {A B} (r : D.Hom A B) →
      (E r C.∘ E (mem A)) C.≈ (E (mem B) C.∘ E (J.F₁ (E r)))
    union-square r = C.transitive (C.symmetric (Functor.composition image _ _))
      (C.transitive (Functor.resp image (Natural.square membership r)) (Functor.composition image _ _))

    -- Flattening the inner families first or the outer family first
    -- agrees. Inside E this is the membership square at membership.
    associative : ∀ X → (μ X C.∘ Pow.F₁ (μ X)) C.≈ (μ X C.∘ μ (Pow.F₀ X))
    associative X = C.transitive (C.symmetric (Functor.composition image _ _))
      (C.transitive (Functor.resp image (D.symmetric (Natural.square membership (mem (J.F₀ X)))))
      (Functor.composition image _ _))
