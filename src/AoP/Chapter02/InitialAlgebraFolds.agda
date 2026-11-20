{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.InitialAlgebraFolds where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.AlgebraCategory using (module For)
open import AoP.Chapter02.UniversalObjects using (module Universal)

-- §2.6. Assume an initial object in Alg(F). Its unique map to each
-- algebra is the fold. Read computation from the square of that map;
-- read reflection and fusion from uniqueness, comparing carrier arrows.
module From {o h e} (C : Category o h e) (F : Functor C C) where
  open Category C
  open For C F
  module U = Universal algebras
  open Algebra
  open Map
  module Laws {I : Algebra} (initial : U.Initial I) where
    fold : ∀ X → Hom (carrier I) (carrier X)
    fold X = arrow (U.Initial.leave initial X)
    computation : ∀ X → fold X ∘ step I ≈ step X ∘ Functor.F₁ F (fold X)
    computation X = square (U.Initial.leave initial X)
    unique : ∀ X (m : Hom (carrier I) (carrier X)) → m ∘ step I ≈ step X ∘ Functor.F₁ F m → m ≈ fold X
    unique X m law = U.Initial.unique initial (hom m law)
    reflection : identity ≈ fold I
    reflection = U.Initial.unique initial (Category.identity algebras)
    fusion : ∀ {X Y} (m : Map X Y) → arrow m ∘ fold X ≈ fold Y
    fusion m = U.Initial.unique initial (paste m (U.Initial.leave initial _))

    -- The inverse of the constructor is a particular fold: take one
    -- layer of the constructor itself as the target algebra. The first
    -- composite is an endomorphism of I, so uniqueness forces identity.
    layer : Algebra
    layer = alg (Functor.F₀ F (carrier I)) (Functor.F₁ F (step I))
    out = fold layer
    roll-out : step I ∘ out ≈ identity
    roll-out = transitive (fusion (hom {X = layer} {Y = I} (step I) reflexive)) (symmetric reflection)
    out-roll : out ∘ step I ≈ identity
    out-roll = transitive (computation layer) (transitive (symmetric (Functor.composition F (step I) out))
      (transitive (Functor.resp F roll-out) (Functor.identity F)))
