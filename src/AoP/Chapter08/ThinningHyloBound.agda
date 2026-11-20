{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ThinningHyloBound where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)
open import AoP.Chapter02.Functors using (Functor)

-- §8.1 Theorem 8.1, coverage half. M constructs a retained parent
-- set, S constructs an exhaustive parent value. E goes from a value
-- to the sets containing it (converse membership). E ∘ Q means that
-- some retained member dominates the rival. Use this composite as
-- the candidate bound in hylomorphism induction.
module Law {o h e p} {C : Category o h e} (L : Laws C p) (F : Functor C C) where
  open Category C
  open Laws L
  private module F = Functor F
  module At {A P} (E : Hom A P) (Q : Hom A A)
    (M : Hom (F.F₀ P) P) (S : Hom (F.F₀ A) A)
    (local-cover : ((M ∘ F.F₁ E) ∘ rev S) ⊑ (E ∘ Q))
    (simulate : (F.F₁ Q ∘ rev S) ⊑ (rev S ∘ Q))
    (trans-Q : (Q ∘ Q) ⊑ Q) where
    B = E ∘ Q
    -- Expose the child comparison, move it through the rival step,
    -- then use the local coverage and compose the two Q witnesses.
    closed : ((M ∘ F.F₁ B) ∘ rev S) ⊑ B
    closed = trans (respect expand) (trans (mono (respect reflexive) simulate)
      (trans (respect (symmetric (assoc _ _ _))) (trans (mono local-cover (respect reflexive))
      (trans (respect (assoc _ _ _)) (mono (respect reflexive) trans-Q)))))
      where
        expand : ((M ∘ F.F₁ B) ∘ rev S) ≈ ((M ∘ F.F₁ E) ∘ (F.F₁ Q ∘ rev S))
        expand = transitive (compose-cong (transitive (compose-cong reflexive (F.composition E Q))
                    (symmetric (assoc _ _ _))) reflexive) (assoc _ _ _)
    coverage : ∀ {I} (retained : Hom I P) (exhaustive : Hom I A) →
      (∀ X → ((M ∘ F.F₁ X) ∘ rev S) ⊑ X → (retained ∘ rev exhaustive) ⊑ X) →
      (retained ∘ rev exhaustive) ⊑ B
    coverage retained exhaustive induct = induct B closed
