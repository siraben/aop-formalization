{-# OPTIONS --safe --without-K #-}
module AoP.PoolPruning where

open import AoP.Prelude
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Thinning using (Thin)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)

-- Compare a candidate against the whole retained suffix. This can
-- prune across intervening incomparable candidates. A candidate is
-- discarded only with evidence of a surviving replacement.
module Sweep {A : Set} (R : A → A → Set) (self : ∀ x → R x x)
             (test : ∀ x y → Dec (R x y)) where
  Witness : A → List A → Set
  Witness x ys = Σ A λ y → (y ∈ ys) × R y x
  find : ∀ x ys → Maybe (Witness x ys)
  find x [] = nothing
  find x (y ∷ ys) with test y x
  ... | inl p = just (y , here , p)
  ... | inr _ with find x ys
  ...   | nothing = nothing
  ...   | just (z , m , p) = just (z , there m , p)
  prune : ∀ xs → Σ (List A) λ ys → Thin R (_∈ ys) (_∈ xs)
  prune [] = [] , record { subset = λ () ; cover = λ _ () }
  prune (x ∷ xs) with prune xs
  ... | ys , good with find x ys
  ...   | just witness = ys , record { subset = λ m → there (Thin.subset good m) ; cover = λ { _ here → witness ; z (there m) → Thin.cover good z m } }
  ...   | nothing = (x ∷ ys) , record { subset = λ { here → here ; (there m) → there (Thin.subset good m) } ; cover = λ { _ here → x , here , self x ; z (there m) → lift (Thin.cover good z m) } }
    where lift : ∀ {z} → Witness z ys → Witness z (x ∷ ys)
          lift (w , m , p) = w , there m , p
