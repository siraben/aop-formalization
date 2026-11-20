{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.SortedImage where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter08.SortedSubset using (module Sort)
open import AoP.Chapter06.OrderedMeet using (module Order)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter05.Subsequences using (_∈_; preimage; image)
open import AoP.Chapter08.Thinning using (Pred)

-- Exercise 8.18, equation 8.8. Sort the source according to its
-- images. Mapping the ordered listing then preserves all required
-- comparisons; coincident images are harmless for set membership.
module Law {A B : Set} (f : A → B) (P : B ← B) where
  pull : A ← A
  pull x y = P (f x) (f y)

  ordered : ∀ {xs} → Order.Ordered pull xs → Order.Ordered P (map f xs)
  ordered Order.nil = Order.nil
  ordered (Order.cons {xs = xs} lower rest) = Order.cons compare (ordered rest)
    where compare : ∀ {b} → b ∈ map f xs → P _ b
          compare m with preimage f xs m
          ... | x , member , refl = lower member

  Image : Pred A → Pred B
  Image X b = Σ A λ a → X a × (f a ≡ b)

  transport : ∀ xs X → Sort.Listing pull xs X → Sort.Listing P (map f xs) (Image X)
  transport xs X (ord , to , from) = ordered ord , forward , backward
    where forward : ∀ b → b ∈ map f xs → Image X b
          forward b m with preimage f xs m
          ... | a , member , refl = a , to a member , refl
          backward : ∀ b → Image X b → b ∈ map f xs
          backward _ (a , x , refl) = image f (from a x)
