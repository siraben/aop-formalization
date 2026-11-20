{-# OPTIONS --safe --without-K #-}
module AoP.EmptyTargets where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 2.21, Fun. Work up to isomorphism of sources: the unique
-- arrow from an initial source or an isomorphism onto the target.
-- For an inhabited target, the constant map from Bool is neither.
InitialSource : Set → Set
InitialSource X = X → ⊥
Invertible : ∀ {X A : Set} → (X → A) → Set
Invertible {X} {A} f = Σ (A → X) λ g → ((x : X) → g (f x) ≡ x) × ((a : A) → f (g a) ≡ a)
EmptyTarget : Set → Set₁
EmptyTarget A = (X : Set) (f : X → A) → InitialSource X ⊎ Invertible f

from-empty : ∀ {A} → (A → ⊥) → EmptyTarget A
from-empty no X f = inl (λ x → no (f x))

private
  clash : ∀ {x : Bool} → x ≡ true → x ≡ false → ⊥
  clash refl ()

to-empty : ∀ {A} → EmptyTarget A → A → ⊥
to-empty e a with e Bool (λ _ → a)
... | inl no = no true
... | inr (g , left , right) = clash (left true) (left false)
