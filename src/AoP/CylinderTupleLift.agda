{-# OPTIONS --safe --without-K #-}
module AoP.CylinderTupleLift where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_)

-- Exercise 7.45. In the derivation of Q, two refinements are lifted
-- through N: extension over minimum (7.13), and minimum over union
-- (7.11). The surrounding equalities that fuse successive N's use
-- preservation of composition. For tuples indexed by rows, these are
-- different operations on witnesses. Neither needs equality on rows.
module Tuple (Row : Set) where
  N : Set → Set
  N A = Row → A
  lift : ∀ {A B} → B ← A → N B ← N A
  lift R ys xs = ∀ i → R (ys i) (xs i)

  monotone : ∀ {A B} {R S : B ← A} → R ⊆ S → lift R ⊆ lift S
  monotone sub p i = sub (p i)
  compose : ∀ {A B C} (S : C ← B) (R : B ← A) → lift S ∘ lift R ⊆ lift (S ∘ R)
  compose S R (middle , s , r) i = middle i , s i , r i
  split : ∀ {A B C} (S : C ← B) (R : B ← A) → lift (S ∘ R) ⊆ lift S ∘ lift R
  split S R p = (λ i → fst (p i)) , (λ i → fst (snd (p i))) , (λ i → snd (snd (p i)))

  -- The extension calculation: a chosen rowwise extension U refines
  -- the rowwise minimum V. Postcomposition with the previously built
  -- tuple of candidate paths preserves that refinement.
  through : ∀ {A B C} (U V : C ← B) (candidates : N B ← A) → U ⊆ V →
            lift U ∘ candidates ⊆ lift V ∘ candidates
  through U V candidates sub (ys , p , g) = ys , monotone {R = U} {S = V} sub p , g
