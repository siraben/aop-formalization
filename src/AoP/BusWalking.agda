{-# OPTIONS --safe --without-K #-}
module AoP.BusWalking where

open import AoP.Prelude
open import AoP.FiniteMinimum using (module Search)
open import AoP.Subsequences using (_∈_; here)
open import AoP.NatOrder using (_≤_)
open import AoP.Polynomial using (inl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _-_)

-- Exercise 8.31. Number block locations from zero, one walking unit
-- apart. Both boarding and alighting passengers use a closest stop.
-- For a supplied nonempty layout the nearest-stop witness also handles
-- ties. This evaluates a layout before optimizing over its locations.
distance : Nat → Nat → Nat
distance j k = (j - k) + (k - j)

module Layout (first : Nat) (rest : List Nat) where
  stops = first ∷ rest
  nearest : ∀ j → Σ Nat λ k → (k ∈ stops) × (∀ l → l ∈ stops → distance j k ≤ distance j l)
  nearest j with M.scan stops
    where module M = Search (λ (_ : Nat) → ⊤) (λ _ → inl tt) (distance j)
  ... | Search.none no with no first here tt
  ...   | ()
  nearest j | Search.best k m _ least = k , m , λ l member → least l member tt

  -- Each pair is (boardings, alightings) at the next block. Both groups
  -- walk the same distance, so each endpoint contributes exactly once.
  walking : Nat → List (Nat × Nat) → Nat
  walking j [] = 0
  walking j ((b , c) ∷ blocks) = (b + c) * distance j (fst (nearest j)) + walking (suc j) blocks

-- Three passengers board at 0. One alights at 1 and two at 2.
-- A single stop at 0 costs five walking units; adding stop 2 costs one.
trips : List (Nat × Nat)
trips = (3 , 0) ∷ (0 , 1) ∷ (0 , 2) ∷ []
one-stop : Layout.walking 0 [] 0 trips ≡ 5
one-stop = refl
two-stops : Layout.walking 0 (2 ∷ []) 0 trips ≡ 1
two-stops = refl
