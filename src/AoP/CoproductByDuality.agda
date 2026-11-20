{-# OPTIONS --safe --without-K #-}
module AoP.CoproductByDuality where

open import AoP.Categories
open import AoP.OppositeCategory using (op)
open import AoP.SpanProduct using (module Over)
open import AoP.SpanProductFunctor using (module Build)

-- §2.5. In the opposite category a span is a pair of injections into
-- a common target. Read the product calculation backwards to obtain
-- coproduct elimination and the action of the coproduct on arrows.
module Dual {o h e} (C : Category o h e) where
  open Category C
  module S = Over (op C)
  module Sum (T : ∀ A B → S.Span A B) (t : ∀ A B → S.U.Terminal A B (T A B)) where
    module D = Build.Chosen (op C) T t
    _⊕_ = D.apex
    inl : ∀ {A B} → Hom A (A ⊕ B)
    inl = D.left _ _
    inr : ∀ {A B} → Hom B (A ⊕ B)
    inr = D.right _ _
    cases : ∀ {A B X} → Hom A X → Hom B X → Hom (A ⊕ B) X
    cases = D.Pair.pair
    cancel-left : ∀ {A B X} (f : Hom A X) (g : Hom B X) → cases f g ∘ inl ≈ f
    cancel-left = D.Pair.cancel-left
    cancel-right : ∀ {A B X} (f : Hom A X) (g : Hom B X) → cases f g ∘ inr ≈ g
    cancel-right = D.Pair.cancel-right
    reflection : ∀ {A B} → identity {A ⊕ B} ≈ cases inl inr
    reflection = D.Pair.unique _ _ _ (unitˡ _) (unitˡ _)
    fusion : ∀ {A B X Y} (m : Hom X Y) (f : Hom A X) (g : Hom B X) →
      m ∘ cases f g ≈ cases (m ∘ f) (m ∘ g)
    fusion m f g = D.fusion f g m
    map : ∀ {A B D E} → Hom A D → Hom B E → Hom (A ⊕ B) (D ⊕ E)
    map = D.cross
    -- After mapping each branch, case analysis just composes the
    -- corresponding branch handlers. This is absorption in op C.
    absorb : ∀ {A B D E X} (f : Hom D X) (g : Hom E X) (h : Hom A D) (k : Hom B E) →
      cases f g ∘ map h k ≈ cases (f ∘ h) (g ∘ k)
    absorb f g h k = D.absorption h k f g
    compose : ∀ {A B D E I J} (g : Hom D I) (k : Hom E J) (f : Hom A D) (h : Hom B E) →
      map g k ∘ map f h ≈ map (g ∘ f) (k ∘ h)
    compose g k f h = D.via-absorption f h g k
