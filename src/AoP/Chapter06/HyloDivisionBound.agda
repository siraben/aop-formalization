{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.HyloDivisionBound where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.ProductAllegory using (Laws)

-- §6.3, Theorem 6.2: the leastness calculation. A producer u goes
-- from inputs to intermediate trees; a consumer c folds those trees.
-- Divide a proposed bound x by u: the result is a bound on c alone,
-- so ordinary fold induction becomes available.
module Law {o h e p} {C : Category o h e} (L : Laws C p) (F : Functor C C)
  (monotone : ∀ {A B} {r s : Category.Hom C A B} → Laws._⊑_ L r s → Laws._⊑_ L (Functor.F₁ F r) (Functor.F₁ F s)) where
  open Category C
  open Laws L
  private module F = Functor F
  module At {A B I} (r : Hom (F.F₀ A) A) (s : Hom B (F.F₀ B)) (out : Hom I (F.F₀ I))
    (c : Hom I A) (u : Hom B I) (unfold : (out ∘ u) ≈ (F.F₁ u ∘ s))
    (induct : ∀ d → ((r ∘ F.F₁ d) ∘ out) ⊑ d → c ⊑ d) where
    -- Fixedness is independent of division. Reassemble the functor
    -- layer and apply the producer and consumer equations in turn.
    fixed : ((r ∘ F.F₁ c) ∘ out) ≈ c → ((r ∘ F.F₁ (c ∘ u)) ∘ s) ≈ (c ∘ u)
    fixed roll = transitive (compose-cong (compose-cong reflexive (F.composition c u)) reflexive)
      (transitive (compose-cong (symmetric (assoc _ _ _)) reflexive) (transitive (assoc _ _ _)
      (transitive (compose-cong reflexive (symmetric unfold)) (transitive (symmetric (assoc _ _ _)) (compose-cong roll reflexive)))))
    module Candidate (x : Hom B A) (pre : ((r ∘ F.F₁ x) ∘ s) ⊑ x)
      (d : Hom I A) (cancel : (d ∘ u) ⊑ x)
      (divide : ∀ k → (k ∘ u) ⊑ x → k ⊑ d) where
      private
        rid : ∀ {X Y} {k : Hom X Y} → k ⊑ k
        rid = respect reflexive
      -- Reassociate the producer square to expose F(d ∘ u), where
      -- division cancellation can be applied under F by monotonicity.
      pass : ((F.F₁ d ∘ out) ∘ u) ≈ (F.F₁ (d ∘ u) ∘ s)
      pass = transitive (assoc _ _ _) (transitive (compose-cong reflexive unfold)
        (transitive (symmetric (assoc _ _ _)) (compose-cong (symmetric (F.composition _ _)) reflexive)))
      rearrange : (((r ∘ F.F₁ d) ∘ out) ∘ u) ≈ ((r ∘ F.F₁ (d ∘ u)) ∘ s)
      rearrange = transitive (compose-cong (assoc _ _ _) reflexive) (transitive (assoc _ _ _)
        (transitive (compose-cong reflexive pass) (symmetric (assoc _ _ _))))
      prefixed : ((r ∘ F.F₁ d) ∘ out) ⊑ d
      prefixed = divide _ (trans (respect rearrange) (trans (mono (mono rid (monotone cancel)) rid) pre))
      least : (c ∘ u) ⊑ x
      least = trans (mono (induct d prefixed) rid) cancel
