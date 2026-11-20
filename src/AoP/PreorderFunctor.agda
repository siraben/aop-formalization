{-# OPTIONS --safe --without-K #-}
module AoP.PreorderFunctor where

open import AoP.Prelude
open import AoP.PreorderCategory using (module Thin)
open import AoP.Functors using (Functor)

-- Exercise 2.10. An arrow records an inequality. Mapping arrows thus
-- says precisely that the object map preserves order. Since all parallel
-- arrows are equivalent, the identity and composition laws cost no extra
-- hypotheses. The correspondence is pointwise on objects.
module Maps {A B : Set} (R : A → A → Set) (S : B → B → Set)
            (rr : ∀ a → R a a) (ss : ∀ b → S b b)
            (rt : ∀ {a b c} → R a b → R b c → R a c)
            (st : ∀ {a b c} → S a b → S b c → S a c) where
  module Source = Thin R rr rt
  module Target = Thin S ss st
  Between = Functor Source.category Target.category

  Monotone : (A → B) → Set
  Monotone f = ∀ {a b} → R a b → S (f a) (f b)

  lift : (f : A → B) → Monotone f → Between
  lift f mono = record { F₀ = f; F₁ = mono; resp = λ _ → tt
                       ; identity = tt; composition = λ _ _ → tt }

  lower : (F : Between) → Monotone (Functor.F₀ F)
  lower F = Functor.F₁ F

  recover : (f : A → B) (m : Monotone f) (a : A) → Functor.F₀ (lift f m) a ≡ f a
  recover f m a = refl
