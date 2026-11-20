{-# OPTIONS --safe --without-K #-}
module AoP.CommonSet where

open import AoP.Prelude
open import AoP.Power using (ℙ; _∈_)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Unit using (⊤; tt)

-- Exercise 7.7. Membership after converse membership relates x to y
-- exactly when there is a set containing both. The unordered pair is
-- a witness, even when x and y coincide. Quantifying over predicates
-- raises the universe of the composite relation.
module Law {A : Set} where
  pair : A → A → ℙ A
  pair x y z = (z ≡ x) ⊎ (z ≡ y)

  Common : A → A → Set₁
  Common x y = Σ (ℙ A) λ s → (x ∈ s) × (y ∈ s)

  universal : ∀ x y → ⊤ → Common x y
  universal x y _ = pair x y , inl refl , inr refl

  forget : ∀ x y → Common x y → ⊤
  forget x y _ = tt
