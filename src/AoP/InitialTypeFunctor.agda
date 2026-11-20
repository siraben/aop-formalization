{-# OPTIONS --safe --without-K #-}
module AoP.InitialTypeFunctor where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.FunctorCategory using (module Construction)
open import AoP.Transformations using (Natural)
open import AoP.ChangeAlgebraParameter using (module Change)
open import AoP.AlgebraCategory using (module For)
open import AoP.InitialAlgebraFolds using (module From)

-- §2.7. Present the layer bifunctor in curried form: each parameter
-- selects an endofunctor; a parameter arrow selects a natural change
-- of layers. Initiality is required only for these selected functors.
module Derive {o h e o′ h′ e′} (P : Category o h e) (C : Category o′ h′ e′)
  (layers : Functor P (Construction.cat C C)) where
  open Category C
  module L = Functor layers
  module Alg X = For C (L.F₀ X)
  module Build (I : ∀ X → Alg.Algebra X) (i : ∀ X → From.U.Initial C (L.F₀ X) (I X)) where
    module F X = From.Laws C (L.F₀ X) (i X)
    carrier : Category.Obj P → Obj
    carrier X = Alg.Algebra.carrier (I X)
    inn : ∀ X → Hom (Functor.F₀ (L.F₀ X) (carrier X)) (carrier X)
    inn X = Alg.Algebra.step (I X)
    action : ∀ {X Y} → Category.Hom P X Y → Hom (carrier X) (carrier Y)
    action {X} {Y} f = Change.Fold.relabel C (L.F₁ f) (i X) (i Y)

    -- One constructor layer contains parameters and recursive fields.
    -- To move that layer along f, first relabel the recursive fields
    -- using the type functor, then change the parameter of the layer.
    layer-action : ∀ {X Y} → Category.Hom P X Y → Hom (Functor.F₀ (L.F₀ X) (carrier X)) (Functor.F₀ (L.F₀ Y) (carrier Y))
    layer-action {X} {Y} f = Natural.η (L.F₁ f) (carrier Y) ∘ Functor.F₁ (L.F₀ X) (action f)

    -- Constructing first and then relabelling gives the same result as
    -- moving the layer first and then using the new constructor. The
    -- fold computation law exposes the two maps in layer-action.
    constructor-square : ∀ {X Y} (f : Category.Hom P X Y) → action f ∘ inn X ≈ inn Y ∘ layer-action f
    constructor-square {X} {Y} f = transitive (F.computation X (Change.pull C (L.F₁ f) (I Y))) (assoc _ _ _)

    -- Equal operations on the same target carrier yield equal folds:
    -- the computation equation for the first also solves the second.
    congruent : ∀ X {Y} (a b : Hom (Functor.F₀ (L.F₀ X) Y) Y) → a ≈ b →
      F.fold X (Alg.alg Y a) ≈ F.fold X (Alg.alg Y b)
    congruent X a b eq = F.unique X _ _ (transitive (F.computation X _) (compose-cong eq reflexive))

    datatype : Functor P C
    Functor.F₀ datatype = carrier
    Functor.F₁ datatype = action
    Functor.resp datatype {X} {Y} eq = congruent X _ _ (compose-cong reflexive (L.resp eq (carrier Y)))
    Functor.identity datatype {X} = transitive (congruent X _ (inn X)
      (transitive (compose-cong reflexive (L.identity (carrier X))) (unitʳ _))) (symmetric (F.reflection X))
    -- Fuse the two folds, reassociate the operations inside the fused
    -- fold, and combine the two changes by functoriality of layers.
    Functor.composition datatype {X} {Y} {Z} g f = symmetric (transitive
      (Change.Fold.consume C (L.F₁ f) (i X) (i Y) (Change.pull C (L.F₁ g) (I Z)))
      (congruent X _ _ (transitive (assoc _ _ _) (compose-cong reflexive (symmetric (L.composition g f (carrier Z)))))))
