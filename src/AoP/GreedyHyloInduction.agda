{-# OPTIONS --safe --without-K #-}
module AoP.GreedyHyloInduction where

open import AoP.Categories
open import AoP.ProductAllegory using (Laws)
open import AoP.Functors using (Functor)

-- §7.2, Theorem 7.2. Compare a greedy derivation with an arbitrary
-- feasible derivation on the same input. Their composite through the
-- input is a hylomorphism. Its induction rule permits R itself as an
-- upper bound, so the proof need only handle one pair of rival layers.
module Law {o h e p} {C : Category o h e} (L : Laws C p) (F : Functor C C) where
  open Category C
  open Laws L
  private module F = Functor F
  module At {A I} (R : Hom A A) (S M : Hom (F.F₀ A) A) (s m : Hom I A)
    (local-best : (M ∘ rev S) ⊑ R) (transitive-R : (R ∘ R) ⊑ R)
    (simulate : (F.F₁ R ∘ rev S) ⊑ (rev S ∘ R)) where
    -- M chooses a minimum among S's results. Simulation moves a
    -- comparison of children to one between parents; local optimality
    -- and transitivity then contract the two parent comparisons.
    closed : ((M ∘ F.F₁ R) ∘ rev S) ⊑ R
    closed = trans (respect (assoc _ _ _)) (trans (mono (respect reflexive) simulate)
      (trans (respect (symmetric (assoc _ _ _))) (trans (mono local-best (respect reflexive)) transitive-R)))
    optimal : (∀ X → ((M ∘ F.F₁ X) ∘ rev S) ⊑ X → (m ∘ rev s) ⊑ X) → (m ∘ rev s) ⊑ R
    optimal induct = induct R closed
    -- Fold monotonicity transports local feasibility M ⊑ S. The
    -- minimum universal property combines it with the rival bound.
    greedy : ∀ {best : Hom I A} → M ⊑ S → (M ⊑ S → m ⊑ s) →
      (∀ X → ((M ∘ F.F₁ X) ∘ rev S) ⊑ X → (m ∘ rev s) ⊑ X) →
      (m ⊑ s → (m ∘ rev s) ⊑ R → m ⊑ best) → m ⊑ best
    greedy valid fold-mono induct introduce = introduce (fold-mono valid) (optimal induct)
