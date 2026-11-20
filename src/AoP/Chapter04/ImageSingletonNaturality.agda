{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.ImageSingletonNaturality where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Transformations using (Natural)
open import AoP.Chapter02.Whiskering using (module Through)
open import AoP.Chapter02.IdentityInitialObject using (module Law)
open import AoP.Chapter04.ExistentialImageFunctor using (module Build)

-- §4.6. Applying existential image to function graphs gives an ordinary
-- powerset functor on functions. The singleton at X is the transpose of
-- the identity relation on J X: its only possible output is the input.
module Derive {o h e o′ h′ e′} (C : Category o h e) (D : Category o′ h′ e′)
  (J : Functor C D) P mem where
  open Build C D J P mem
  module GivenLaws (laws : ∀ A → U.Laws A) where
    open Given laws
    private module C = Category C
    private module D = Category D
    private module J = Functor J
    power = Through.compose J image
    -- The membership naturality square is just transpose cancellation
    -- read backwards, using the definition E r = Λ (r ∘ mem).
    membership : Natural (Through.compose image J) (Law.Id D)
    Natural.η membership = mem
    Natural.square membership r = D.symmetric (L.cancel _ _)

    singleton : Natural (Law.Id C) power
    Natural.η singleton X = Λ {X = X} D.identity
    Natural.square singleton {X} {Y} f = C.transitive (absorb (J.F₁ f) D.identity)
      (C.transitive (congruent (D.transitive (D.unitʳ _) (D.symmetric (D.unitˡ _))))
      (C.symmetric (U.Derived.fusion (J.F₀ Y) (laws _) (S.obj Y D.identity) f)))
