{-# OPTIONS --safe --without-K #-}
module AoP.SubsetBounds where

open import AoP.Prelude
open import AoP.Relations

-- Exercises 7.1–7.2. A lower bound for a superset bounds each of
-- its subsets; the subset itself is a witness for the reverse law.
module Law {A B : Set} (R : B ← A) where
  Lower : B → (A → Set) → Set
  Lower b X = ∀ a → X a → R b a

  via-superset : ∀ {b X} → (Σ (A → Set) λ Y → (∀ a → X a → Y a) × Lower b Y) → Lower b X
  via-superset (Y , sub , bound) a xa = bound a (sub a xa)

  self : ∀ {b X} → Lower b X → Σ (A → Set) λ Y → (∀ a → X a → Y a) × Lower b Y
  self {X = X} bound = X , (λ _ x → x) , bound

  -- Y is a subset of the existential image of X exactly when every
  -- member of Y can be reached through R from some member of X.
  Image : (A → Set) → B → Set
  Image X b = Σ A λ a → R b a × X a

  module ImageSubset (X : A → Set) (Y : B → Set) where
    Through : Set₁
    Through = Σ (B → Set) λ Z → (∀ b → Y b → Z b) ×
                ((∀ b → Z b → Image X b) × (∀ b → Image X b → Z b))

    eliminate : Through → ∀ b → Y b → Image X b
    eliminate (Z , sub , out , _) b y = out b (sub b y)

    introduce : (∀ b → Y b → Image X b) → Through
    introduce sub = Image X , sub , (λ _ p → p) , (λ _ p → p)
