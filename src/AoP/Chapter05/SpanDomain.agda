{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.SpanDomain where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)

-- Exercise 5.5. The domain test of a relation presented by rows is
-- exactly the image of the input column. Its proof explains why the
-- other column must be entire: no row may lose its output witness.
module Law {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  dom : ∀ {A B} → Hom A B → Hom A A
  dom r = meet (rev r ∘ r) identity
  private
    rid : ∀ {A B} {f : Hom A B} → f ⊑ f
    rid = respect reflexive
  congruent : ∀ {A B} {r s : Hom A B} → r ≈ s → dom r ≈ dom s
  congruent {r = r} {s} eq = antisym (one eq) (one (symmetric eq))
    where
      one : ∀ {A B} {x y : Hom A B} → x ≈ y → dom x ⊑ dom y
      one p = glb (trans (lower₁ _ _) (mono (rev-mono (respect p)) (respect p))) (lower₂ _ _)
  module Row {I A B} (f : Hom I B) (g : Hom I A) (entire : identity ⊑ (rev f ∘ f)) (simple : (g ∘ rev g) ⊑ identity) where
    r = f ∘ rev g
    mid = rev f ∘ r
    swap : rev r ≈ (g ∘ rev f)
    swap = transitive (flip _ _) (compose-cong (invol _) reflexive)
    path : (rev r ∘ r) ≈ (g ∘ mid)
    path = transitive (compose-cong swap reflexive) (assoc _ _ _)
    -- Modular restriction of this return path to identity keeps only
    -- rows whose input is the same at both ends.
    shrink : dom r ⊑ (g ∘ rev g)
    shrink = trans (glb (trans (lower₁ _ _) (respect path)) (lower₂ _ _))
      (trans (modular g mid identity) (mono rid (trans (lower₂ _ _) (respect (unitʳ _)))))
    -- Insert a round trip through the output column between g and g˘.
    grow : (g ∘ rev g) ⊑ dom r
    grow = glb (trans (mono rid (trans (respect (symmetric (unitˡ _)))
      (trans (mono entire rid) (respect (assoc _ _ _))))) (respect (symmetric path))) simple
    domain : dom r ≈ (g ∘ rev g)
    domain = antisym shrink grow
