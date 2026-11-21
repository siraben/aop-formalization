{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.AlgebraMinimumComparison where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.ProductAllegory using (Laws)

-- Theorem 7.1, the relational calculation. Membership m and minimum
-- w go from a power object to its elements. The key §7.1 identity
-- w ∘ m˘ ≈ R says that comparing a minimum with a rival recovers R.
module Law {o h e p} {C : Category o h e} (L : Laws C p) (F : Functor C C) where
  open Category C
  open Laws L
  private module F = Functor F
  open ArrowReasoning C
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
    compare =
      chosen ∘ rev feasible                         ≈⟨ compose-cong reflexive (flip alg _) ⟩
      chosen ∘ (rev (F.F₁ m) ∘ rev alg)             ≈⟨ symmetric (assoc _ _ _) ⟩
      (chosen ∘ rev (F.F₁ m)) ∘ rev alg             ≈⟨ compose-cong inner reflexive ⟩
      (alg ∘ F.F₁ R) ∘ rev alg                     ∎≈
      where inner : ((alg ∘ F.F₁ w) ∘ rev (F.F₁ m)) ≈ (alg ∘ F.F₁ R)
            inner =
              (alg ∘ F.F₁ w) ∘ rev (F.F₁ m)    ≈⟨ assoc _ _ _ ⟩
              alg ∘ (F.F₁ w ∘ rev (F.F₁ m))    ≈⟨ compose-cong reflexive (compose-cong reflexive turn) ⟩
              alg ∘ (F.F₁ w ∘ F.F₁ (rev m))    ≈⟨ compose-cong reflexive (symmetric (F.composition _ _)) ⟩
              alg ∘ F.F₁ (w ∘ rev m)           ≈⟨ compose-cong reflexive (F.resp recover) ⟩
              alg ∘ F.F₁ R                     ∎≈
    -- State the minimum universal property at the one fibre used by
    -- the theorem. No global powerset or resizing axiom is required.
    module Fibre (best : Hom (F.F₀ P) A)
      (optimal : chosen ⊑ best → (chosen ∘ rev feasible) ⊑ R)
      (introduce : chosen ⊑ feasible → (chosen ∘ rev feasible) ⊑ R → chosen ⊑ best) where
      distributes : ((alg ∘ F.F₁ R) ∘ rev alg) ⊑ R → chosen ⊑ best
      distributes bound = introduce include (trans (respect compare) bound)
      monotone-algebra : chosen ⊑ best → ((alg ∘ F.F₁ R) ∘ rev alg) ⊑ R
      monotone-algebra law = trans (respect (symmetric compare)) (optimal law)
