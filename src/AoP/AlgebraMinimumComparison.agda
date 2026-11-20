{-# OPTIONS --safe --without-K #-}
module AoP.AlgebraMinimumComparison where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.ProductAllegory using (Laws)

-- Theorem 7.1, the relational calculation. Membership m and minimum
-- w go from a power object to its elements. The key §7.1 identity
-- w ∘ m˘ ≈ R says that comparing a minimum with a rival recovers R.
module Law {o h e p} {C : Category o h e} (L : Laws C p) (F : Functor C C) where
  open Category C
  open Laws L
  private module F = Functor F
  module At {A P} (m w : Hom P A) (R : Hom A A) (alg : Hom (F.F₀ A) A)
    (recover : (w ∘ rev m) ≈ R) (contained : w ⊑ m)
    (monoF : ∀ {X Y} {r s : Hom X Y} → r ⊑ s → F.F₁ r ⊑ F.F₁ s)
    (turn : rev (F.F₁ m) ≈ F.F₁ (rev m)) where
    chosen = alg ∘ F.F₁ w
    feasible = alg ∘ F.F₁ m
    -- Feasibility is automatic: every selected child is a member.
    include : chosen ⊑ feasible
    include = mono (respect reflexive) (monoF contained)
    -- Optimality compares the selected result with *all* feasible
    -- rivals. First expose the two lifted legs in the middle, then
    -- combine them into F(w ∘ m˘), which is just F R.
    compare : (chosen ∘ rev feasible) ≈ ((alg ∘ F.F₁ R) ∘ rev alg)
    compare = transitive (compose-cong reflexive (flip alg _))
      (transitive (symmetric (assoc _ _ _)) (compose-cong inner reflexive))
      where inner : ((alg ∘ F.F₁ w) ∘ rev (F.F₁ m)) ≈ (alg ∘ F.F₁ R)
            inner = transitive (assoc _ _ _) (compose-cong reflexive (transitive
              (compose-cong reflexive turn) (transitive (symmetric (F.composition _ _)) (F.resp recover))))
    -- State the minimum universal property at the one fibre used by
    -- the theorem. No global powerset or resizing axiom is required.
    module Fibre (best : Hom (F.F₀ P) A)
      (optimal : chosen ⊑ best → (chosen ∘ rev feasible) ⊑ R)
      (introduce : chosen ⊑ feasible → (chosen ∘ rev feasible) ⊑ R → chosen ⊑ best) where
      distributes : ((alg ∘ F.F₁ R) ∘ rev alg) ⊑ R → chosen ⊑ best
      distributes bound = introduce include (trans (respect compare) bound)
      monotone-algebra : chosen ⊑ best → ((alg ∘ F.F₁ R) ∘ rev alg) ⊑ R
      monotone-algebra law = trans (respect (symmetric compare)) (optimal law)
