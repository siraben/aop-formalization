{-# OPTIONS --safe --without-K #-}
module AoP.FunStrength where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.MapNaturality using (transport)

-- Exercise 3.40, positive direction. The arrow action of any endofunctor
-- on Fun is itself a function between function spaces. Its naturality
-- in the source and target follows from functorial composition twice,
-- generalizing the preceding list-map calculation.
module Strength (F : Functor Fun Fun) where
  open Functor F using (F₀; F₁; composition)
  lift : ∀ {A B} → (A → B) → F₀ A → F₀ B
  lift = F₁

  square : ∀ {A B C D} (pre : C → A) (post : B → D) (f : A → B) (x : F₀ C) →
           lift (transport pre post f) x ≡ transport (lift pre) (lift post) (lift f) x
  square pre post f x = begin
    lift (transport pre post f) x ≡⟨ composition post (λ c → f (pre c)) x ⟩
    lift post (lift (λ c → f (pre c)) x) ≡⟨ cong (lift post) (composition f pre x) ⟩
    transport (lift pre) (lift post) (lift f) x ∎
