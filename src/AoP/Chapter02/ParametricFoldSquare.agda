{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ParametricFoldSquare where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Transformations using (Natural)
open import AoP.Chapter02.ChangeAlgebraParameter using (module Change)
open import AoP.Chapter02.InitialAlgebraFolds using (module From)
open import AoP.Chapter02.AlgebraCategory using (module For)

-- Exercise 2.39, one arbitrary naturality square in any category C.
-- A change α of layer may come from applying the parameter functor G
-- to the source arrow. The two target algebras interpret the layers
-- at its endpoints; h is the action of the result functor H on it.
module Square {o e k} (C : Category o e k) {F G : Functor C C} (α : Natural F G) where
  open Category C
  module S = For C F
  module T = For C G
  module Shift = Change C α
  module Proof {I J} (i : From.U.Initial C F I) (j : From.U.Initial C G J)
    (X : S.Algebra) (Y : T.Algebra) (h : Hom (S.Algebra.carrier X) (T.Algebra.carrier Y))
    (natural-algebra : h ∘ S.Algebra.step X ≈ S.Algebra.step (Shift.pull Y) ∘ Functor.F₁ F h) where
    module L = From.Laws C F i
    module R = From.Laws C G j
    module M = Shift.Fold i j
    -- Both routes are the unique fold into the pulled-back algebra.
    -- On the left use the algebra square on h; on the right use the
    -- consumer/parameter fusion equation (2.14) in reverse.
    commute : h ∘ L.fold X ≈ R.fold Y ∘ M.relabel
    commute = transitive (L.fusion (S.hom h natural-algebra)) (symmetric (M.consume Y))
