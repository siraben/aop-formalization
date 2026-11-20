{-# OPTIONS --safe --without-K #-}
module AoP.IdentityInitialObject where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.UniversalObjects using (module Universal)
open import AoP.AlgebraCategory using (module For)

-- Exercise 2.33 in an arbitrary category. A unary operation on an
-- initial object is forced to equal identity. Conversely an initial
-- identity-algebra must have an initial carrier: its operation is an
-- algebra endomorphism, hence coincides with the identity endomorphism.
module Law {o h e} (C : Category o h e) where
  open Category C
  Id : Functor C C
  Functor.F₀ Id X = X
  Functor.F₁ Id f = f
  Functor.resp Id p = p
  Functor.identity Id = reflexive
  Functor.composition Id g f = reflexive
  open For C Id
  module U = Universal C
  module V = Universal algebras

  forward : ∀ {I} → U.Initial I → V.Initial (alg I identity)
  Map.arrow (V.Initial.leave (forward i) (alg X s)) = U.Initial.leave i X
  Map.square (V.Initial.leave (forward i) (alg X s)) = transitive (U.Initial.unique i _) (symmetric (U.Initial.unique i _))
  V.Initial.unique (forward i) m = U.Initial.unique i (Map.arrow m)

  module Reverse {I} {s : Hom I I} (i : V.Initial (alg I s)) where
    operation-id : s ≈ identity
    operation-id = transitive (V.Initial.unique i (hom s reflexive)) (symmetric (V.Initial.unique i (Category.identity algebras)))
    -- Any carrier map now respects the unary operations into (X,id).
    backward : U.Initial I
    U.Initial.leave backward X = Map.arrow (V.Initial.leave i (alg X identity))
    U.Initial.unique backward f = V.Initial.unique i (hom f (transitive (compose-cong reflexive operation-id)
      (transitive (unitʳ f) (symmetric (unitˡ f)))))
