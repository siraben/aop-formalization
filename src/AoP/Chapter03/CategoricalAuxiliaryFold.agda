{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.CategoricalAuxiliaryFold where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.SpanProduct using (module Over)
open import AoP.Chapter02.AlgebraCategory using (module For)
open import AoP.Chapter02.InitialAlgebraFolds using (module From)

-- Exercise 3.4. The answer at a parent may depend on both parts of
-- each child's cached pair. Only the auxiliary computation is independent.
module Law {o h e} (C : Category o h e) (F : Functor C C) where
  open Category C
  open For C F
  module F = Functor F
  module Cache {I} (i : From.U.Initial C F I) (B : Algebra) (A : Obj) where
    open From.Laws C F i
    open Algebra
    module S = Over C A (carrier B)
    module Build {P} (t : S.U.Terminal P) where
      open S.Pair t using (pair; cancel-left; cancel-right)
      p = S.Span.apex P
      l = S.Span.left P
      r = S.Span.right P
      module Derive (answer : Hom (carrier I) A) (g : Hom (F.F₀ p) A)
        (law : answer ∘ step I ≈ g ∘ F.F₁ (pair answer (fold B))) where
        both = pair answer (fold B)
        joint = alg p (pair g (step B ∘ F.F₁ r))
        -- Observe the candidate through a projection. Reassociation
        -- exposes its selected component on each side of the square.
        branch : ∀ {X} (proj : Hom p X) (a : Hom (carrier I) X) (k : Hom (F.F₀ p) X) →
          proj ∘ both ≈ a → proj ∘ step joint ≈ k → a ∘ step I ≈ k ∘ F.F₁ both →
          proj ∘ (both ∘ step I) ≈ proj ∘ (step joint ∘ F.F₁ both)
        branch proj a k read update eq = transitive (symmetric (assoc _ _ _))
          (transitive (compose-cong read reflexive) (transitive eq
          (transitive (compose-cong (symmetric update) reflexive) (assoc _ _ _))))
        -- The right branch follows just from fold computation and
        -- functoriality: projecting each child recovers its auxiliary fold.
        aux : fold B ∘ step I ≈ (step B ∘ F.F₁ r) ∘ F.F₁ both
        aux = transitive (computation B) (transitive (compose-cong reflexive (F.resp (symmetric (cancel-right _ _))))
          (transitive (compose-cong reflexive (F.composition r both)) (symmetric (assoc _ _ _))))
        invariant : both ≈ fold joint
        invariant = unique joint both (transitive (S.Pair.unique t _ _ _
          (branch l answer g (cancel-left _ _) (cancel-left _ _) law)
          (branch r (fold B) _ (cancel-right _ _) (cancel-right _ _) aux))
          (symmetric (S.Pair.unique t _ _ _ reflexive reflexive)))
        result : answer ≈ l ∘ fold joint
        result = transitive (symmetric (cancel-left _ _)) (compose-cong reflexive invariant)
