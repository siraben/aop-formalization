{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.LatenessPick where

open import AoP.Common.Prelude
open import AoP.Chapter10.SignedLateness using (charge)
open import AoP.Chapter07.SignedSegment using (_≤_; rid; cmp; chain)
open import AoP.Chapter10.Tardiness using (Job)
open import AoP.Chapter05.Permutations using (Insert; front; later)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- Compare signed penalties at the common finish time. Even when all
-- jobs finish early, the selector retains their distinct negative costs.
record Pick (t : Nat) (xs : List Job) : Set where
  constructor picked
  field last : Job
        others : List Job
        occurrence : Insert last others xs
        least : ∀ x → x ∈ xs → charge last t ≤ charge x t

pick : ∀ t j js → Pick t (j ∷ js)
pick t j [] = picked j [] front λ { _ here → rid _ ; _ (there ()) }
pick t j (k ∷ ks) with pick t k ks
... | picked z zs slot best with cmp (charge j t) (charge z t)
...   | inl le = picked j (k ∷ ks) front λ { _ here → rid _ ; x (there m) → chain le (best x m) }
...   | inr ge = picked z (j ∷ zs) (later slot) λ { _ here → ge ; x (there m) → best x m }
