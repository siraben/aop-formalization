{-# OPTIONS --safe --without-K #-}
module AoP.EntabPending where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import AoP.Complement using (⊥)
open import AoP.Detab
open import AoP.Entab
open import AoP.TabFree

-- For a given output prefix, position counts how many *extra* blanks
-- its next tab will consume beyond one. The encoder must never buffer
-- one blank too many: that would have passed a stop without emitting a
-- tab. This invariant concerns internal buffer state, not just decoding.
step-below : ∀ {i j} → i ≤ j → (i ≡ j → ⊥) → suc i ≤ j
step-below {zero} {zero} _ no with no refl
... | ()
step-below {zero} {suc j} _ no = s≤ z≤
step-below {suc i} {suc j} (s≤ le) no = s≤ (step-below le (λ eq → no (cong suc eq)))

module Stops {A : Set} (n : Nat) where
  open Expand {A} n
  open Encode {A} n
  open Image {A} n

  Bounded : ∀ {s} → Buffer s → Set
  Bounded b = Buffer.pending b ≤ position (detab (Buffer.code b))

  advance-bound : ∀ {s} (b : Buffer s) → Bounded b → Bounded (add-space b)
  advance-bound (buf xs k inv) le with test k (position (detab xs))
  ... | same refl = z≤
  ... | different no = step-below le no

  bounded : ∀ {s} (p : Plain s) → Bounded (encode p)
  bounded empty = z≤
  bounded (space p) = advance-bound (encode p) (bounded p)
  bounded (line p) = z≤
  bounded (char a p) = z≤
