{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ConstantInitial where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Initial using (module Theory)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter02.SwapNatural using (Pairs; Types; Maps)
open Types using (L; R)
open Maps using (left; right)

-- Exercise 2.38. If a layer ignores its recursive slot, its initial
-- carrier is the layer itself. An algebra K → A already specifies the
-- output at every possible input. The identity constructor exposes the
-- entire input in one step, so folding is just applying that algebra.
module Constant (K : Set) where
  F : Functor Fun Fun
  Functor.F₀ F _ = K
  Functor.F₁ F _ k = k
  Functor.resp F _ k = refl
  Functor.identity F k = refl
  Functor.composition F _ _ k = refl

  open Theory F
  algebra : Initial
  Initial.μ algebra = K
  Initial.inn algebra k = k
  Initial.⦅_⦆ algebra a = a
  Initial.computation algebra a k = refl
  Initial.unique algebra a h hom k = hom k

-- In the example the parameter is a pair of types. The layer consists
-- of a choice of one of their elements. Varying the pair therefore
-- gives the sum functor Fun × Fun → Fun, mapping only the chosen side.
Sum : Functor Pairs Fun
Functor.F₀ Sum p = L p ⊎ R p
Functor.F₁ Sum f (inl a) = inl (left f a)
Functor.F₁ Sum f (inr b) = inr (right f b)
Functor.resp Sum (p , q) (inl a) = cong inl (p a)
Functor.resp Sum (p , q) (inr b) = cong inr (q b)
Functor.identity Sum (inl a) = refl
Functor.identity Sum (inr b) = refl
Functor.composition Sum g f (inl a) = refl
Functor.composition Sum g f (inr b) = refl

initial-at : ∀ p → Theory.Initial (Constant.F (Functor.F₀ Sum p))
initial-at p = Constant.algebra (Functor.F₀ Sum p)
