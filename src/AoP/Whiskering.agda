{-# OPTIONS --safe --without-K #-}
module AoP.Whiskering where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.Transformations using (Natural)

module Through {o h e o′ h′ e′ o″ h″ e″} {A : Category o h e}
               {B : Category o′ h′ e′} {C : Category o″ h″ e″} (H : Functor A B) where
  -- Precompose an object map and its arrow map with H. Each composite
  -- functor law uses the law for H followed by the corresponding law
  -- for F; respect for arrow equality lets F transport the first step.
  compose : Functor B C → Functor A C
  compose F = record
    { F₀ = λ x → F.F₀ (H.F₀ x); F₁ = λ f → F.F₁ (H.F₁ f)
    ; resp = λ eq → F.resp (H.resp eq)
    ; identity = Cat.transitive (F.resp H.identity) F.identity
    ; composition = λ g f → Cat.transitive (F.resp (H.composition g f))
                                           (F.composition (H.F₁ g) (H.F₁ f)) }
    where
    module H = Functor H
    module F = Functor F
    module Cat = Category C

  -- Exercise 2.17. To move the new component across f, use the old
  -- square at H f. The component at x was the old component at H x.
  whisker : ∀ {F G} → Natural F G → Natural (compose F) (compose G)
  Natural.η (whisker α) x = Natural.η α (Functor.F₀ H x)
  Natural.square (whisker α) f = Natural.square α (Functor.F₁ H f)
