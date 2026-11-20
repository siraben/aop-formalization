{-# OPTIONS --safe --without-K #-}
module AoP.PartitionThree where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat)
open import AoP.Paragraph using (Nonempty; _∷⁺_)
open import AoP.PartitionFlatten using (module Law)
open Law Nat using (partitions)

-- §5.6 worked example. The two gaps in [1,2,3] can each be cut or
-- left uncut. Name all four layouts so the computed enumeration checks
-- both the contents of each block and the absence of extra results.
separate cut-first cut-last together : List (Nonempty Nat)
separate = (1 ∷⁺ []) ∷ (2 ∷⁺ []) ∷ (3 ∷⁺ []) ∷ []
cut-first = (1 ∷⁺ []) ∷ (2 ∷⁺ (3 ∷ [])) ∷ []
cut-last = (1 ∷⁺ (2 ∷ [])) ∷ (3 ∷⁺ []) ∷ []
together = (1 ∷⁺ (2 ∷ 3 ∷ [])) ∷ []

example : partitions (1 ∷ 2 ∷ 3 ∷ []) ≡ separate ∷ cut-first ∷ cut-last ∷ together ∷ []
example = refl
