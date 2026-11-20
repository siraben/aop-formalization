{-# OPTIONS --safe --without-K #-}
module AoP.FlattenConverseLaw where

open import AoP.Prelude
open import AoP.Trees using (Tree; tip; bin)
open import AoP.BracketSpine using (leaves; peel; Place; preserves)
open import AoP.ConverseNonempty using (module Law)
open import AoP.Polynomial using (_⊎_; inl; inr)

-- Exercise 9.14: instantiate the converse function theorem. The
-- algebra either creates a tip or inserts a leaf along the left spine.
-- Surjectivity follows by peeling; the compatibility inclusions reduce
-- to the singleton equation and the insertion preservation equation.
module Flatten {A : Set} where
  Tip : A → Tree A → Set
  Tip a t = tip a ≡ t
  onto : ∀ t → (Σ A λ a → Tip a t) ⊎ (Σ A λ a → Σ (Tree A) λ r → Place a r t)
  onto (tip x) = inl (x , refl)
  onto (bin l r) = inr (peel l r)
  singleton : ∀ {a t} → Tip a t → leaves t ≡ a ∷ []
  singleton refl = refl
  module Converse = Law leaves Tip Place onto singleton preserves
  -- The two directions are the relational equality flatten° = fold.
  fold-in = Converse.complete
  fold-out = Converse.sound
