{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ChangeAlgebraParameter where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Transformations using (Natural)
open import AoP.Chapter02.AlgebraCategory using (module For)
open import AoP.Chapter02.InitialAlgebraFolds using (module From)

-- §2.7. A parameter change is a natural transformation between the
-- two layer functors. Pull a target algebra back across it: first
-- change labels in the layer, then interpret that layer as before.
module Change {o h e} (C : Category o h e) {F G : Functor C C} (α : Natural F G) where
  open Category C
  module S = For C F
  module T = For C G
  module α = Natural α
  pull : T.Algebra → S.Algebra
  pull (T.alg X a) = S.alg X (a ∘ α.η X)

  -- Naturality lets the carrier arrow cross the parameter change.
  lift : ∀ {X Y} → T.Map X Y → S.Map (pull X) (pull Y)
  S.Map.arrow (lift m) = T.Map.arrow m
  S.Map.square (lift {T.alg X a} {T.alg Y b} (T.hom m sq)) =
    transitive (symmetric (assoc m a _)) (transitive (compose-cong sq reflexive)
    (transitive (assoc b _ _) (transitive (compose-cong reflexive (α.square m)) (symmetric (assoc b _ _)))))

  module Fold {I J} (i : From.U.Initial C F I) (j : From.U.Initial C G J) where
    module L = From.Laws C F i
    module R = From.Laws C G j
    -- (2.13): specialize the source fold to the pulled-back constructor.
    relabel = L.fold (pull J)
    -- The key fusion step for the type functor proof: a consumer after
    -- relabelling is the source fold into the pulled-back consumer algebra.
    consume : ∀ X → R.fold X ∘ relabel ≈ L.fold (pull X)
    consume X = L.fusion (lift (From.U.Initial.leave j X))
