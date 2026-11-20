{-# OPTIONS --safe --without-K #-}
module AoP.PrefixScoreGreedy where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.GreedyFold using (module Lists)

-- Exercise 7.40, greedy-theorem step. Prefix sums either reset to
-- zero or add the new head. A larger retained score simulates either
-- branch, since adding a common head preserves the comparison.
module Law {A : Set} (zero : A) (_+_ : A → A → A) (_≤_ : A → A → Set)
           (rid : ∀ a → a ≤ a) (tr : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
           (cmp : ∀ a b → (a ≤ b) ⊎ (b ≤ a))
           (mono : ∀ x {a b} → a ≤ b → (x + a) ≤ (x + b)) where
  data Step : A ← (A × A) where
    reset : ∀ {x p} → Step zero (x , p)
    add : ∀ {x p} → Step (x + p) (x , p)
  Better : A ← A
  Better a b = b ≤ a
  match : ∀ {x b c z} → Better b c → Step z (x , c) → Σ A λ y → Step y (x , b) × Better y z
  match h reset = zero , reset , rid zero
  match h (add {x}) = _ , add , mono x h
  module G = Lists Better (λ p q → tr q p) (λ a → a ≡ zero) Step match

  fold-best : ∀ xs → Σ A λ a → G.Greedy a xs
  fold-best [] = zero , G.seed (refl , λ { _ refl → rid zero })
  fold-best (x ∷ xs) with fold-best xs
  ... | p , g with cmp zero (x + p)
  ...   | inl h = (x + p) , G.step g (add , λ { _ reset → h ; _ add → rid _ })
  ...   | inr h = zero , G.step g (reset , λ { _ reset → rid _ ; _ add → h })

  bound : ∀ xs {p} → Fold (λ a → a ≡ zero) Step p xs → p ≤ fst (fold-best xs)
  bound xs = G.bound (snd (fold-best xs))
