{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.PairMembers where

open import AoP.Common.Prelude
open import AoP.Chapter05.Subsequences using (_∈_; here; there; split; preimage)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter08.OrderedPairs using (pairs)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter08.TraceCardinality using (module Count)
open import AoP.Chapter08.MinimalQueries using (module Solver)
open import AoP.Chapter08.HiddenTrace using (module Law)

-- Every pair produced by the enumeration is a query about two input
-- members. With fresh input elements its endpoints are distinct, so
-- the hidden-comparison adversary forces it onto the solver's trace.
module Members {A : Set} where
  open Count {A}
  endpoints : ∀ {a b xs} → Distinct xs → (a , b) ∈ pairs xs →
              (a ∈ xs) × ((b ∈ xs) × (a ≡ b → ⊥))
  endpoints nil ()
  endpoints (cons {x} {xs} fresh d) m with split (map (x ,_) xs) (map (_, x) xs ++ pairs xs) m
  ... | inl pm with preimage (x ,_) xs pm
  ...   | b , present , refl = here , there present , λ { refl → fresh present }
  endpoints (cons {x} {xs} fresh d) m | inr rest with split (map (_, x) xs) (pairs xs) rest
  ... | inl pm with preimage (_, x) xs pm
  ...   | a , present , refl = there present , here , λ { refl → fresh present }
  endpoints (cons {x} {xs} fresh d) m | inr rest | inr old with endpoints d old
  ... | a∈ , b∈ , ne = there a∈ , there b∈ , ne

  open import AoP.Chapter02.Polynomial using (_⊎_)
  module Required (dec : ∀ (x y : A) → (x ≡ y) ⊎ (x ≡ y → ⊥)) (xs : List A) (d : Distinct xs) where
    open Solver dec xs
    open Law dec using (module T; equal)
    includes : ∀ p → Correct p → ∀ q → q ∈ pairs xs → q ∈ T.trace equal p
    includes p ok (a , b) m with endpoints d m
    ... | ax , bx , ne = Adversary.must-query a b ne p ok ax bx
