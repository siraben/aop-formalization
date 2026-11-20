{-# OPTIONS --safe --without-K #-}
module AoP.DomainPullback where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (graph)
open import AoP.RangeRotation using (ran)
private variable A B C : Set

-- Exercise 4.17. To check whether f(a) lies in the domain of R,
-- one can first test whether a lies in the domain of the composite,
-- then return f(a). The same R-output witnesses either domain test.
dom : (B ← A) → A ← A
dom R = ran (R ˘)

module Test (R : C ← B) (f : A → B) where
  F = graph f

  pull : dom R ∘ F ⊆ F ∘ dom (R ∘ F)
  pull {a = a} (_ , (refl , c , r) , refl) = a , refl , refl , c , f a , r , refl

  push : F ∘ dom (R ∘ F) ⊆ dom R ∘ F
  push {a = a} (_ , refl , refl , c , _ , r , refl) = f a , (refl , c , r) , refl
