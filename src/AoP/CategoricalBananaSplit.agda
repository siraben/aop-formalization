{-# OPTIONS --safe --without-K #-}
module AoP.CategoricalBananaSplit where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.SpanProduct using (module Over)
open import AoP.AlgebraCategory using (module For)
open import AoP.InitialAlgebraFolds using (module From)

-- §3.1. Pair two folds on the same initial algebra. The combined
-- operation projects each recursive result through F before applying
-- its own consumer. Only the product of the two result objects is used.
module Law {o h e} (C : Category o h e) (F : Functor C C) where
  open Category C
  open For C F
  module F = Functor F
  module PairFolds {I} (i : From.U.Initial C F I) (X Y : Algebra) where
    open From.Laws C F i
    open Algebra
    module S = Over C (carrier X) (carrier Y)
    module Product {P} (t : S.U.Terminal P) where
      open S.Pair t
      l = S.Span.left P
      r = S.Span.right P
      operation = pair (step X ∘ F.F₁ l) (step Y ∘ F.F₁ r)
      joint = alg (S.Span.apex P) operation
      -- Either projection is a homomorphism from the joint algebra:
      -- cancelling a projection of operation leaves its own branch.
      left-fold : l ∘ fold joint ≈ fold X
      left-fold = fusion (hom l (cancel-left _ _))
      right-fold : r ∘ fold joint ≈ fold Y
      right-fold = fusion (hom r (cancel-right _ _))
      split : pair (fold X) (fold Y) ≈ fold joint
      split = symmetric (S.Pair.unique t _ _ _ left-fold right-fold)

      -- The calculation in §3.1 takes the other direction: prove that
      -- the pair of separate folds already solves the joint fold equation.
      candidate = pair (fold X) (fold Y)
      -- Observe either component of either side of that equation.
      -- Fold computation exposes its consumer; functor composition then
      -- restores the projection of the candidate inside the layer.
      observe : ∀ Z (p : Hom (S.Span.apex P) (carrier Z)) → p ∘ candidate ≈ fold Z →
        p ∘ operation ≈ step Z ∘ F.F₁ p → p ∘ (candidate ∘ step I) ≈ p ∘ (operation ∘ F.F₁ candidate)
      observe Z p select update = transitive (symmetric (assoc _ _ _))
        (transitive (compose-cong select reflexive) (transitive (computation Z)
        (transitive (compose-cong reflexive (F.resp (symmetric select)))
        (transitive (compose-cong reflexive (F.composition p candidate))
        (transitive (symmetric (assoc _ _ _)) (transitive (compose-cong (symmetric update) reflexive) (assoc _ _ _)))))))
      direct : candidate ≈ fold joint
      direct = From.Laws.unique C F i joint candidate (transitive
        (S.Pair.unique t _ _ _ (observe X l (cancel-left _ _) (cancel-left _ _))
                               (observe Y r (cancel-right _ _) (cancel-right _ _)))
        (symmetric (S.Pair.unique t _ _ _ reflexive reflexive)))
