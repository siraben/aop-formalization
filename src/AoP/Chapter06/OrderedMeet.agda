{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.OrderedMeet where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊓_; _∘_; _⊆_)
open import AoP.Chapter05.Subsequences using (_∈_)

-- Exercise 6.24. Orderedness compares every earlier element with each
-- later one. Filtering by R and then by S compares exactly the same
-- pairs twice, so the tests can be combined pointwise. No transitivity,
-- totality or comparison decision is needed for this equality.
module Order {A : Set} where
  data Ordered (R : A ← A) : List A → Set where
    nil : Ordered R []
    cons : ∀ {a xs} → (∀ {b} → b ∈ xs → R a b) → Ordered R xs → Ordered R (a ∷ xs)

  ordered : (A ← A) → List A ← List A
  ordered R ys xs = (ys ≡ xs) × Ordered R xs

  both : ∀ {R S xs} → Ordered R xs → Ordered S xs → Ordered (R ⊓ S) xs
  both nil nil = nil
  both (cons r rs) (cons s ss) = cons (λ m → r m , s m) (both rs ss)

  project : ∀ {R S xs} → R ⊆ S → Ordered R xs → Ordered S xs
  project f nil = nil
  project f (cons r rs) = cons (λ m → f (r m)) (project f rs)

  combine : ∀ R S → ordered R ∘ ordered S ⊆ ordered (R ⊓ S)
  combine R S (_ , (refl , r) , refl , s) = refl , both r s

  separate : ∀ R S → ordered (R ⊓ S) ⊆ ordered R ∘ ordered S
  separate R S (refl , o) = _ , (refl , project fst o) , refl , project snd o
