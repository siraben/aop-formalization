{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.ProductComparison where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)

-- Exercise 3.2. For an endofunctor F, observe a value of F(A × B)
-- through both mapped projections. This gives a comparison from the
-- bifunctor (A,B) ↦ F(A × B) to (A,B) ↦ FA × FB. It need not be an
-- isomorphism. Naturality says independent changes of A and B commute
-- with these two observations.
module Comparison {o h e} (C : Category o h e) (F : Functor C C) where
  open Category C
  open Functor F using (F₀; F₁; resp; composition)
  module Chosen (_⊗_ : Obj → Obj → Obj)
    (l : ∀ {A B} → Hom (A ⊗ B) A) (r : ∀ {A B} → Hom (A ⊗ B) B)
    (pair : ∀ {X A B} → Hom X A → Hom X B → Hom X (A ⊗ B))
    (pl : ∀ {X A B} (a : Hom X A) (b : Hom X B) → l ∘ pair a b ≈ a)
    (pr : ∀ {X A B} (a : Hom X A) (b : Hom X B) → r ∘ pair a b ≈ b)
    (ext : ∀ {X A B} (f g : Hom X (A ⊗ B)) → l ∘ f ≈ l ∘ g → r ∘ f ≈ r ∘ g → f ≈ g) where
    cross : ∀ {A B X Y} → Hom A X → Hom B Y → Hom (A ⊗ B) (X ⊗ Y)
    cross f g = pair (f ∘ l) (g ∘ r)
    φ : ∀ {A B} → Hom (F₀ (A ⊗ B)) (F₀ A ⊗ F₀ B)
    φ = pair (F₁ l) (F₁ r)

    observe : ∀ {X Y Z W} (p : Hom Z W) (s : Hom Y Z) (t : Hom X Y) {v} → p ∘ s ≈ v → p ∘ (s ∘ t) ≈ v ∘ t
    observe p s t eq = transitive (symmetric (assoc p s t)) (compose-cong eq reflexive)

    natural : ∀ {A B X Y} (f : Hom A X) (g : Hom B Y) → φ ∘ F₁ (cross f g) ≈ cross (F₁ f) (F₁ g) ∘ φ
    natural f g = ext _ _ first second
      where
      first = transitive (observe l φ _ (pl _ _)) (transitive (symmetric (composition l _))
        (transitive (resp (pl _ _)) (transitive (composition f l)
        (symmetric (transitive (observe l _ φ (pl _ _)) (transitive (assoc _ l φ) (compose-cong reflexive (pl _ _))))))))
      second = transitive (observe r φ _ (pr _ _)) (transitive (symmetric (composition r _))
        (transitive (resp (pr _ _)) (transitive (composition g r)
        (symmetric (transitive (observe r _ φ (pr _ _)) (transitive (assoc _ r φ) (compose-cong reflexive (pr _ _))))))))
