{-# OPTIONS --safe --without-K #-}
module AoP.FibreBounds where

open import AoP.Relations
open import AoP.Power using (ℙ; Λ)

-- Exercise 4.50. Recover an edge from the sets that contain its whole
-- output fibre. If b belongs to every such set, use the fibre itself
-- as the test set. Conversely an edge transports into any upper bound.
-- Spell out the two divisions: membership's source ℙ B is large.
module Law {A B : Set} (R : B ← A) where
  -- R ＼ ∈ : input a is related to a set X when its fibre lies in X.
  bound : A → ℙ B → Set
  bound a X = ∀ {b} → R b a → X b

  -- ∈ ／ (R ＼ ∈) : b belongs to each bound of the fibre at a.
  tested : B → A → Set₁
  tested b a = (X : ℙ B) → bound a X → X b

  introduce : ∀ {a b} → R b a → tested b a
  introduce edge X contains = contains edge

  recover : ∀ {a b} → tested b a → R b a
  recover {a} all = all (Λ R a) (λ edge → edge)
