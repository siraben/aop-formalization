{-# OPTIONS --safe --without-K #-}
module AoP.ThinLayerFusion where

open import AoP.Categories
open import AoP.ProductAllegory using (Laws)
open import AoP.Functors using (Functor)
import AoP.ThinningHyloBound as Bound

-- Theorem 8.1: instantiate both one-layer tests with generation
-- followed by pruning. G collects all feasible parents in a set,
-- T chooses a thinning of it, and mem reads an element of a set.
module Law {o h e p} {C : Category o h e} (L : Laws C p) (F : Functor C C) where
  open Category C
  open Laws L
  private module F = Functor F
  module Run {A P} (mem : Hom P A) (Q : Hom A A) (T : Hom P P)
    (S : Hom (F.F₀ A) A) (G : Hom (F.F₀ P) P)
    (members : (mem ∘ T) ⊑ mem) (covers : (T ∘ rev mem) ⊑ (rev mem ∘ Q))
    (generated : (mem ∘ G) ⊑ (S ∘ F.F₁ mem))
    (collect : ((G ∘ F.F₁ (rev mem)) ∘ rev S) ⊑ rev mem)
    (simulate : (F.F₁ Q ∘ rev S) ⊑ (rev S ∘ Q)) (trans-Q : (Q ∘ Q) ⊑ Q) where
    M = T ∘ G
    -- Read a retained member, forget pruning, then unpack generation.
    layer-sub : (mem ∘ M) ⊑ (S ∘ F.F₁ mem)
    layer-sub = trans (respect (symmetric (assoc _ _ _))) (trans (mono members (respect reflexive)) generated)
    -- A rival with children from these sets occurs in the generated
    -- set. The coverage half of thinning gives a retained dominator.
    layer-cover : ((M ∘ F.F₁ (rev mem)) ∘ rev S) ⊑ (rev mem ∘ Q)
    layer-cover = trans (respect (compose-cong (assoc _ _ _) reflexive)) (trans (respect (assoc _ _ _))
      (trans (mono (respect reflexive) collect) covers))
    module H = Bound.Law.At L F (rev mem) Q M S layer-cover simulate trans-Q

    module Result {I} (m : Hom I P) (s : Hom I A)
      (fusion : (mem ∘ M) ⊑ (S ∘ F.F₁ mem) → (mem ∘ m) ⊑ s)
      (induct : ∀ X → ((M ∘ F.F₁ X) ∘ rev S) ⊑ X → (m ∘ rev s) ⊑ X) where
      feasible : (mem ∘ m) ⊑ s
      feasible = fusion layer-sub
      coverage : (m ∘ rev s) ⊑ (rev mem ∘ Q)
      coverage = H.coverage m s induct
      theorem : ∀ {thin-fibre : Hom I P} →
        ((mem ∘ m) ⊑ s → (m ∘ rev s) ⊑ (rev mem ∘ Q) → m ⊑ thin-fibre) → m ⊑ thin-fibre
      theorem introduce = introduce feasible coverage
