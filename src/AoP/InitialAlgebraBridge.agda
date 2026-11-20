{-# OPTIONS --safe --without-K #-}
module AoP.InitialAlgebraBridge where

open import AoP.Categories using (Fun)
open import AoP.AlgebraCategory using (module For)
open import AoP.Functors using (Functor)
open import AoP.Initial using (module Theory)
open import AoP.UniversalObjects using (module Universal)
open import AoP.ListAlgebra using (module Cons)

-- §2.6. Connect the executable presentation of an initial algebra in
-- Fun to initiality in the category of algebras. Both use pointwise
-- arrow equality. No change to the underlying fold program is needed.
module Bridge (F : Functor Fun Fun) where
  open For Fun F
  module U = Universal algebras
  module T = Theory F
  expose : (i : T.Initial) → U.Initial (alg (T.Initial.μ i) (T.Initial.inn i))
  Map.arrow (U.Initial.leave (expose i) (alg A act)) = T.Initial.⦅_⦆ i act
  Map.square (U.Initial.leave (expose i) (alg A act)) = T.Initial.computation i act
  U.Initial.unique (expose i) {alg A act} (hom h eq) = T.Initial.unique i act h eq

  internalize : ∀ {X} → U.Initial X → T.Initial
  T.Initial.μ (internalize {X} i) = Algebra.carrier X
  T.Initial.inn (internalize {X} i) = Algebra.step X
  T.Initial.⦅_⦆ (internalize i) act = Map.arrow (U.Initial.leave i (alg _ act))
  T.Initial.computation (internalize i) act = Map.square (U.Initial.leave i (alg _ act))
  T.Initial.unique (internalize i) act h eq = U.Initial.unique i (hom h eq)

-- Specialize to character lists for the string example. The two tags
-- select a seed and a step that consumes the head and the folded tail.
open import Agda.Builtin.Char using (Char)
open import AoP.Polynomial using (roll)
open import AoP.Prelude using (List)
module StringExample where
  open For (Fun) (Cons.layerF Char)
  module U = Universal algebras
  initial : U.Initial (alg (List Char) roll)
  initial = Bridge.expose (Cons.layerF Char) (Cons.initial Char)
