{-# OPTIONS --safe --without-K #-}
module AoP.FilterMap where

open import AoP.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import AoP.Horner using (map)
open import AoP.PointFree using (wrapIf; filter)
open import AoP.Functors using (map-comp; map-resp)
open import AoP.Naturality using (concat; concat-natural)

-- Exercise 3.30. To filter the image of a list, test each original
-- element with the composite predicate and map just the survivors.
-- Expand filter into singleton-or-empty contributions, then move map
-- past concat. The only case analysis concerns a single contribution.
module Derive {A B : Set} (f : A → B) (p : B → Bool) where
  keep : A → List A
  keep x = wrapIf (p (f x)) x
  selected : B → List B
  selected y = wrapIf (p y) y

  contribution : ∀ x → selected (f x) ≡ map f (keep x)
  contribution x with p (f x)
  ... | true = refl
  ... | false = refl

  private
    back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    back refl = refl

  calculate : ∀ xs → filter p (map f xs) ≡ map f (filter (λ x → p (f x)) xs)
  calculate xs = begin
    concat (map selected (map f xs)) ≡⟨ cong concat (back (map-comp selected f xs)) ⟩
    concat (map (λ x → selected (f x)) xs) ≡⟨ cong concat (map-resp contribution xs) ⟩
    concat (map (λ x → map f (keep x)) xs) ≡⟨ cong concat (map-comp (map f) keep xs) ⟩
    concat (map (map f) (map keep xs)) ≡⟨ back (concat-natural f (map keep xs)) ⟩
    map f (filter (λ x → p (f x)) xs) ∎
