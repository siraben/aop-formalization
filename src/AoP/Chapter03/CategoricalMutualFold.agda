{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.CategoricalMutualFold where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.SpanProduct using (module Over)
open import AoP.Chapter02.AlgebraCategory using (module For)
open import AoP.Chapter02.InitialAlgebraFolds using (module From)

-- Exercise 3.8. Both updates can inspect both child results. Each
-- projection of the fold equation is one recurrence. Conversely the
-- projections determine the entire arrow into the product.
module Law {o h e} (C : Category o h e) (F : Functor C C) where
  open Category C
  open For C F
  module F = Functor F
  module Solve {I} (i : From.U.Initial C F I) (A B : Obj) where
    open From.Laws C F i
    module S = Over C A B
    module Joint {P} (prod : S.U.Terminal P) where
      open S.Pair prod using (pair; cancel-left; cancel-right)
      T = Algebra.carrier I
      inn = Algebra.step I
      U = S.Span.apex P
      module Test (f : Hom T A) (g : Hom T B) (a : Hom (F.F₀ U) A) (b : Hom (F.F₀ U) B) where
        answers = pair f g
        update = pair a b
        target = alg U update
        lhs = answers ∘ inn
        rhs = update ∘ F.F₁ answers
        -- Express each side as a pair. The same product law applies
        -- to both, irrespective of which algebra operation follows.
        distribute : ∀ {X Y} (p : Hom X A) (q : Hom X B) (m : Hom Y X) → pair p q ∘ m ≈ pair (p ∘ m) (q ∘ m)
        distribute p q m = S.Pair.unique prod _ _ _
          (transitive (symmetric (assoc _ _ _)) (compose-cong (cancel-left _ _) reflexive))
          (transitive (symmetric (assoc _ _ _)) (compose-cong (cancel-right _ _) reflexive))
        combine : f ∘ inn ≈ a ∘ F.F₁ answers → g ∘ inn ≈ b ∘ F.F₁ answers → answers ≈ fold target
        combine p q = unique target answers (transitive (distribute f g inn) (transitive
          (S.Pair.unique prod _ _ _ (transitive (cancel-left _ _) p) (transitive (cancel-right _ _) q))
          (symmetric (distribute a b _))))
        square : answers ≈ fold target → lhs ≈ rhs
        square eq = transitive (compose-cong eq reflexive) (transitive (computation target)
          (compose-cong reflexive (F.resp (symmetric eq))))
        observe : ∀ {Z} (p : Hom U Z) (v : Hom T Z) (k : Hom (F.F₀ U) Z) → p ∘ answers ≈ v → p ∘ update ≈ k →
          answers ≈ fold target → v ∘ inn ≈ k ∘ F.F₁ answers
        observe p v k read branch eq = transitive (compose-cong (symmetric read) reflexive)
          (transitive (assoc _ _ _) (transitive (compose-cong reflexive (square eq))
          (transitive (symmetric (assoc _ _ _)) (compose-cong branch reflexive))))
        first = observe (S.Span.left P) f a (cancel-left _ _) (cancel-left _ _)
        second = observe (S.Span.right P) g b (cancel-right _ _) (cancel-right _ _)
