{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.BusProfileDecision where

open import AoP.Common.Prelude
open import AoP.Chapter08.BusProfile
open import AoP.Chapter08.Bump using (module Prune)
open import AoP.Chapter08.ParagraphMinimum using (Dec; le?)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter05.Subsequences using (here; there)
open import AoP.Common.NatOrder using (rid; chain)
open import Agda.Builtin.Nat using (Nat)

-- Decide the universal profile comparison by visiting the finite list
-- of demand blocks. One failed distance comparison rules it out.
profile? : ∀ js l r → Dec (Profile js l r)
profile? [] l r = inl λ _ ()
profile? (j ∷ js) l r with le? (near l j) (near r j)
... | inr no = inr (λ p → no (p j here))
... | inl bound with profile? js l r
...   | inr no = inr (λ p → no (λ i m → p i (there m)))
...   | inl rest = inl λ { _ here → bound ; i (there m) → rest i m }

module Frontier (js : List Nat) where
  module P = Prune (Profile js) (λ _ _ _ → rid _) (λ p q j m → chain (p j m) (q j m))
  compare : ∀ l r → P.Comparison l r
  compare l r with profile? js l r
  ... | inl p = P.first p
  ... | inr _ with profile? js r l
  ...   | inl p = P.second p
  ...   | inr _ = P.retain
  module Thin = P.Algorithm compare

-- On a block with demand only at 2, [2] dominates [0]. With demand
-- at both ends, neither singleton is dispensable by this test.
pruned : Frontier.Thin.thinlist (2 ∷ []) (sites 0 [] ∷ sites 2 [] ∷ []) ≡ sites 2 [] ∷ []
pruned = refl
retained : Frontier.Thin.thinlist (0 ∷ 2 ∷ []) (sites 0 [] ∷ sites 2 [] ∷ []) ≡ sites 0 [] ∷ sites 2 [] ∷ []
retained = refl
