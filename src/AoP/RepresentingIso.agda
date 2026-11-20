{-# OPTIONS --safe --without-K #-}
module AoP.RepresentingIso where

open import AoP.Categories using (Category)

-- The final object-level step in a distributivity calculation. If maps
-- out of P correspond naturally and invertibly to maps out of Q, apply
-- the correspondence to the two identities to obtain inverse arrows.
module Law {o h e} (C : Category o h e) where
  open Category C
  module Identify (P Q : Obj)
    (to : ∀ {T} → Hom P T → Hom Q T) (from : ∀ {T} → Hom Q T → Hom P T)
    (to-resp : ∀ {T} {f g : Hom P T} → f ≈ g → to f ≈ to g)
    (from-resp : ∀ {T} {f g : Hom Q T} → f ≈ g → from f ≈ from g)
    (section : ∀ {T} (f : Hom Q T) → to (from f) ≈ f)
    (retract : ∀ {T} (f : Hom P T) → from (to f) ≈ f)
    (to-natural : ∀ {S T} (u : Hom S T) (f : Hom P S) → to (u ∘ f) ≈ u ∘ to f)
    (from-natural : ∀ {S T} (u : Hom S T) (f : Hom Q S) → from (u ∘ f) ≈ u ∘ from f) where
    forward : Hom P Q
    forward = from identity
    backward : Hom Q P
    backward = to identity

    forward-back : forward ∘ backward ≈ identity
    forward-back = transitive (symmetric (to-natural forward identity))
                   (transitive (to-resp (unitʳ forward)) (section identity))
    back-forward : backward ∘ forward ≈ identity
    back-forward = transitive (symmetric (from-natural backward identity))
                   (transitive (from-resp (unitʳ backward)) (retract identity))
