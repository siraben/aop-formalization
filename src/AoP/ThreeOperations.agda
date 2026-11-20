{-# OPTIONS --safe --without-K #-}
module AoP.ThreeOperations where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)

-- Exercise 2.32. A constructor may add a B on the left, add a C on
-- the right, or finish with a B. The tag tells a single algebra which
-- of its three operations to use. Only the recursive slot changes
-- when a function is mapped across one layer.
module Signature (B C : Set) where
  data Layer (X : Set) : Set where
    prefix : B × X → Layer X
    suffix : X × C → Layer X
    finish : B → Layer X

  F : Functor Fun Fun
  Functor.F₀ F = Layer
  Functor.F₁ F h (prefix (b , x)) = prefix (b , h x)
  Functor.F₁ F h (suffix (x , c)) = suffix (h x , c)
  Functor.F₁ F h (finish b) = finish b
  Functor.resp F eq (prefix (b , x)) = cong (λ y → prefix (b , y)) (eq x)
  Functor.resp F eq (suffix (x , c)) = cong (λ y → suffix (y , c)) (eq x)
  Functor.resp F eq (finish b) = refl
  Functor.identity F (prefix _) = refl
  Functor.identity F (suffix _) = refl
  Functor.identity F (finish _) = refl
  Functor.composition F g f (prefix _) = refl
  Functor.composition F g f (suffix _) = refl
  Functor.composition F g f (finish _) = refl

  module Algebra {A : Set} (f₀ : B × A → A) (f₁ : A × C → A) (f₂ : B → A) where
    g : Layer A → A
    g (prefix p) = f₀ p
    g (suffix p) = f₁ p
    g (finish b) = f₂ b

    prefix-law : ∀ p → g (prefix p) ≡ f₀ p
    prefix-law p = refl
    suffix-law : ∀ p → g (suffix p) ≡ f₁ p
    suffix-law p = refl
    finish-law : ∀ b → g (finish b) ≡ f₂ b
    finish-law b = refl
