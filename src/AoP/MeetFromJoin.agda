{-# OPTIONS --safe --without-K #-}
module AoP.MeetFromJoin where

open import AoP.Prelude
open import AoP.AdjointJoins using (Joins)

-- Exercise 4.28. In a small ordered carrier admitting indexed joins,
-- collect all common lower bounds of the given family. Their join
-- still lies below each family member, because that member bounds
-- every candidate. Every common lower bound occurs among the candidates.
module Construct {P : Set} (J : Joins P) {I : Set} (family : I → P) where
  open Joins J
  Lower : Set
  Lower = Σ P (λ x → ∀ i → x ≤ family i)

  value : Lower → P
  value = fst
  meet : P
  meet = sup value

  projection : ∀ i → meet ≤ family i
  projection i = least value (family i) (λ candidate → snd candidate i)

  greatest : ∀ x → (∀ i → x ≤ family i) → x ≤ meet
  greatest x all = member value (x , all)

  -- The empty family needs no special clause: every x qualifies as
  -- a candidate, so its meet is a greatest element.
