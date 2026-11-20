{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.IdentityAlgebra where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Initial using (module Theory)
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 2.33. An algebra for identity is a type A with one unary
-- operation A → A. With no nullary constructor, no finite term can
-- ever be started. The empty type therefore carries the initial algebra:
-- its unique function to A vacuously respects every unary operation.
Identity : Functor Fun Fun
Functor.F₀ Identity A = A
Functor.F₁ Identity f = f
Functor.resp Identity eq = eq
Functor.identity Identity _ = refl
Functor.composition Identity _ _ _ = refl

open Theory Identity
initial : Initial
Initial.μ initial = ⊥
Initial.inn initial x = x
Initial.⦅_⦆ initial alg ()
Initial.computation initial alg ()
Initial.unique initial alg h hom ()
