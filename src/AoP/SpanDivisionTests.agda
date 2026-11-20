{-# OPTIONS --safe --without-K #-}
module AoP.SpanDivisionTests where

open import AoP.Categories
open import AoP.ProductAllegory using (Laws)
open import AoP.SpanColumnShunt using (module Law)

-- §4.6. On a span of maps, the two division tests reduce to equality
-- of its observed columns. The second test runs backwards, so first
-- reverse the span. This swaps its legs without changing its row type.
module In {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  module Div (under : ∀ {X Y Z} → Hom Y Z → Hom X Z → Hom X Y)
    (intro : ∀ {X Y Z} (r : Hom Y Z) (s : Hom X Z) (x : Hom X Y) → (r ∘ x) ⊑ s → x ⊑ under r s)
    (elim : ∀ {X Y Z} (r : Hom Y Z) (s : Hom X Z) (x : Hom X Y) → x ⊑ under r s → (r ∘ x) ⊑ s) where
    module Test {I A B P} (mem : Hom P A) (R : Hom B A) (f : Hom I P) (g : Hom I B)
      (fu : identity ⊑ (rev f ∘ f)) (fc : (f ∘ rev f) ⊑ identity)
      (gu : identity ⊑ (rev g ∘ g)) (gc : (g ∘ rev g) ⊑ identity) where
      module F = Law.Move L f fu fc
      module G = Law.Move L g gu gc
      span = f ∘ rev g
      opposite = g ∘ rev f
      tests = meet (under mem R) (rev (under R mem))
      turn : rev span ≈ opposite
      turn = transitive (flip f (rev g)) (compose-cong (invol g) reflexive)
      read : span ⊑ tests → (mem ∘ f) ≈ (R ∘ g)
      read sub = antisym (G.column mem f R (elim _ _ _ (trans sub (lower₁ _ _))))
        (F.column R g mem (elim _ _ _ (trans (respect (symmetric turn))
          (trans (rev-mono (trans sub (lower₂ _ _))) (respect (invol _))))))
      write : (mem ∘ f) ≈ (R ∘ g) → span ⊑ tests
      write eq = glb (intro _ _ _ (G.span mem f R (respect eq)))
        (trans (respect (symmetric (invol span))) (rev-mono (trans (respect turn)
          (intro _ _ _ (F.span R g mem (respect (symmetric eq)))))))
