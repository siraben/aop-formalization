{-# OPTIONS --safe --without-K #-}
module AoP.LaxChoices where

open import AoP.Prelude
open import AoP.Power using (ℙ)
open import AoP.PowerRelator using (Lift; cover)
open import AoP.SingletonTranspose using (unit)
open import AoP.TransposeCombinations using (cup)
open import AoP.Polynomial using (inl; inr)
open import AoP.Relations
open import AoP.RelationalProducts using (_⊗_)
open import AoP.Shunting using (graph)

-- Exercise 5.30. A single output choice can be wrapped or duplicated;
-- lifting after wrapping or duplicating also permits independent choices.
-- Two independent covers can be combined into a cover of the union.
module Law {A B : Set} (R : B ← A) where
  singleton : ∀ {b a} → R b a → Lift R (unit b) (unit a)
  singleton {b} {a} r = cover (λ { _ refl → a , refl , r }) (λ { _ refl → b , refl , r })

  dup : ∀ {X : Set} → X → X × X
  dup x = x , x
  duplicate : graph dup ∘ R ⊆ (R ⊗ R) ∘ graph dup
  duplicate (_ , refl , r) = _ , (r , r) , refl

  union : ∀ {Y V : ℙ B} {X U : ℙ A} → Lift R Y X → Lift R V U → Lift R (cup (Y , V)) (cup (X , U))
  Lift.backward (union l r) b (inl y) with Lift.backward l b y
  ... | a , x , e = a , inl x , e
  Lift.backward (union l r) b (inr v) with Lift.backward r b v
  ... | a , u , e = a , inr u , e
  Lift.forward (union l r) a (inl x) with Lift.forward l a x
  ... | b , y , e = b , inl y , e
  Lift.forward (union l r) a (inr u) with Lift.forward r a u
  ... | b , v , e = b , inr v , e
