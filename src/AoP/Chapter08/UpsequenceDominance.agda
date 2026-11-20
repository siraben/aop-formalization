{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.UpsequenceDominance where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; rid; chain; s≤)
open import AoP.Chapter01.ConversionCost using (len)

-- Exercise 8.29. Scan right to left. A suffix candidate may replace
-- another if it is at least as long and accepts every preceding value
-- the other accepts. For instance [4,6] can replace [3,7]: both have
-- length two and anything at most 3 is also at most 4.
module Law {A : Set} (R : A → A → Set) where
  Accept : A → List A → Set
  Accept a [] = ⊤
  Accept a (b ∷ _) = R a b
  data Ordered : List A → Set where
    nil : Ordered []
    cons : ∀ {a xs} → Accept a xs → Ordered xs → Ordered (a ∷ xs)

  Dominates : List A → List A → Set
  Dominates xs ys = (len ys ≤ len xs) × (∀ a → Accept a ys → Accept a xs)
  reflexive : ∀ xs → Dominates xs xs
  reflexive xs = rid _ , λ _ ok → ok
  transitive : ∀ xs ys zs → Dominates xs ys → Dominates ys zs → Dominates xs zs
  transitive xs ys zs (p , f) (q , g) = chain q p , λ a ok → f a (g a ok)

  -- Skipping a value changes neither candidate. Taking it preserves
  -- feasibility and dominance: both extended lists have the same head.
  take-step : ∀ a xs ys → Dominates xs ys → Ordered xs → Accept a ys →
              Ordered (a ∷ xs) × Dominates (a ∷ xs) (a ∷ ys)
  take-step a xs ys (le , permit) sorted ok = cons (permit a ok) sorted , s≤ le , λ _ p → p
