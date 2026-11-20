{-# OPTIONS --safe --without-K #-}
module AoP.NonlinearChoices where

open import AoP.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.OrderedMeet using (module Order)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Complement using (⊥)
open import AoP.PolynomialChoices using (menu)

-- Exercise 8.21. Even allowing a different enumeration order cannot
-- repair (8.11) for I × I. Every ordered listing compares any two
-- members, but the product of two sorted Boolean menus must contain
-- both (false,true) and (true,false), which are incomparable.
comparable : ∀ {A : Set} {P : A → A → Set} → (∀ a → P a a) → ∀ {xs a b} → Order.Ordered P xs →
         a ∈ xs → b ∈ xs → P a b ⊎ P b a
comparable rr (Order.cons low rest) here here = inl (rr _)
comparable rr (Order.cons low rest) here (there n) = inl (low n)
comparable rr (Order.cons low rest) (there m) here = inr (low m)
comparable rr (Order.cons low rest) (there m) (there n) = comparable rr rest m n

data Le : Bool → Bool → Set where
  same : ∀ {a} → Le a a
  rise : Le false true

sorted : Order.Ordered Le menu
sorted = Order.cons (λ { here → rise ; (there ()) }) (Order.cons (λ ()) Order.nil)

Product : Bool × Bool → Bool × Bool → Set
Product p q = Le (fst p) (fst q) × Le (snd p) (snd q)

impossible : ∀ xs → Order.Ordered Product xs → (false , true) ∈ xs → (true , false) ∈ xs → ⊥
impossible xs sorted p q with comparable (λ _ → same , same) sorted p q
... | inl (_ , ())
... | inr (() , _)
