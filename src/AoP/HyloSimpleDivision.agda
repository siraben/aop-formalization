{-# OPTIONS --safe --without-K #-}
module AoP.HyloSimpleDivision where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.ProductAllegory using (Laws)

-- Exercise 6.10. Instead of comparing trees, induct on one run
-- while keeping the whole rival relation H fixed. The division
-- id / H˘ collects precisely the comparisons that already imply
-- agreement of outputs. This works for an arbitrary base relator.
module Law {o h e p} {C : Category o h e} (L : Laws C p) (F : Functor C C) where
  open Category C
  open Laws L
  private module F = Functor F
  private
    rid : ∀ {A B} {x : Hom A B} → x ⊑ x
    rid = respect reflexive
    turn : ∀ {A B} {x y : Hom A B} → x ≈ y → rev x ≈ rev y
    turn eq = antisym (rev-mono (respect eq)) (rev-mono (respect (symmetric eq)))
  module At {A B} (r : Hom (F.F₀ A) A) (s : Hom B (F.F₀ B)) (h : Hom B A)
    (rs : (r ∘ rev r) ⊑ identity) (ss : (s ∘ rev s) ⊑ identity) where
    step : Hom B A → Hom B A
    step x = (r ∘ F.F₁ x) ∘ s
    module Induct (fixed : h ≈ step h) (least : ∀ x → step x ⊑ x → h ⊑ x)
      (d : Hom B A) (cancel : (d ∘ rev h) ⊑ identity)
      (divide : ∀ x → (x ∘ rev h) ⊑ identity → x ⊑ d)
      (monoF : ∀ {X Y} {u v : Hom X Y} → u ⊑ v → F.F₁ u ⊑ F.F₁ v)
      (converse : F.F₁ (rev h) ≈ rev (F.F₁ h)) where
      -- After reversing the rival step, the two producer edges are
      -- adjacent. Contract them using simplicity, then compare children.
      rival : rev h ≈ (rev s ∘ (rev (F.F₁ h) ∘ rev r))
      rival = transitive (turn fixed) (transitive (flip _ _) (compose-cong reflexive (flip _ _)))
      erase : ∀ {X} (k : Hom X (F.F₀ B)) → (s ∘ (rev s ∘ k)) ⊑ k
      erase k = trans (respect (symmetric (assoc _ _ _))) (trans (mono ss rid) (respect (unitˡ _)))
      children : (F.F₁ d ∘ rev (F.F₁ h)) ⊑ identity
      children = trans (mono rid (respect (symmetric converse)))
        (trans (respect (symmetric (F.composition _ _))) (trans (monoF cancel) (respect F.identity)))
      -- Now the consumer round trip is all that remains.
      parent : ((r ∘ F.F₁ d) ∘ (rev (F.F₁ h) ∘ rev r)) ⊑ identity
      parent = trans (respect (assoc _ _ _)) (trans (mono rid (trans (respect (symmetric (assoc _ _ _)))
        (trans (mono children rid) (respect (unitˡ _))))) rs)
      closed : step d ⊑ d
      closed = divide _ (trans (mono rid (respect rival)) (trans (respect (assoc _ _ _))
        (trans (mono rid (erase _)) parent)))
      simple : (h ∘ rev h) ⊑ identity
      simple = trans (mono (least d closed) rid) cancel
