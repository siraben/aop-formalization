{-# OPTIONS --safe --without-K #-}
module AoP.ThinFibreCalculation where

open import AoP.Prelude
open import AoP.Relations using (_←_; _∘_)
open import AoP.Thinning using (Pred; Thin; thin; Min)

-- §8.1. A program X may return different retained sets at input i.
-- Test the universal property (8.1) by considering one such set U.
-- The first inclusion checks every member of U; the second inclusion
-- matches every rival output of S at the *same* input.
module Fibre {A I : Set} (Q : A ← A) (S : A ← I) (X : Pred A → I → Set) where
  Valid = ∀ U i → X U i → Thin Q U (λ a → S a i)
  Feasible = ∀ U i → X U i → ∀ a → U a → S a i
  Dominates = ∀ U i → X U i → ∀ b → S b i → Σ A λ a → U a × Q a b

  members : Valid → Feasible
  members valid U i x a = Thin.subset (valid U i x)
  bounds : Valid → Dominates
  bounds valid U i x = Thin.cover (valid U i x)
  introduce : Feasible → Dominates → Valid
  introduce sub match U i x = thin (sub U i x _) (match U i x)

-- (8.3). The comparison used to take a minimum need imply Q only on
-- pairs that can actually arise together. Return the singleton winner;
-- the rival and winner supply the common-input witness for the guard.
module Singleton {A I : Set} (R Q : A ← A) (S : A ← I)
  (guard : ∀ a b → R a b → (Σ I λ i → S a i × S b i) → Q a b) where
  eliminate : ∀ i w → Min R w (λ a → S a i) → Thin Q (λ a → a ≡ w) (λ a → S a i)
  eliminate i w (sw , wins) = thin (λ { refl → sw })
    (λ b sb → w , refl , guard w b (wins b sb) (i , sw , sb))
