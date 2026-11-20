{-# OPTIONS --safe --without-K #-}
module AoP.DivisionStability where

open import AoP.Prelude
open import AoP.Relations using (_←_; _∘_; _⊆_; _˘; _／_)
open import AoP.Complement using (¬_; module BooleanDivision)
open import AoP.Shunting using (Id)

-- §4.5. Exactly where is the Boolean hypothesis in (4.21) needed?
-- Fix the numerator X and vary the denominator Y. Stability of the
-- edges of X suffices for the reverse inclusion, and testing that same
-- inclusion just at identity recovers stability at every edge.
module Fixed {A C : Set} (X : C ← A) where
  Stable = ¬ (¬ X) ⊆ X
  Reverse : ∀ {B : Set} → B ← A → Set
  Reverse Y = ¬ ((¬ X) ∘ Y ˘) ⊆ X ／ Y

  sufficient : Stable → ∀ {B : Set} (Y : B ← A) → Reverse Y
  sufficient stable Y = BooleanDivision.backward X Y stable

  necessary : Reverse Id → Stable
  necessary at-id nn = at-id (λ { (_ , nx , refl) → nn nx }) refl
