{-# OPTIONS --safe --without-K #-}
module AoP.PickLast where

open import AoP.Prelude
open import AoP.Tardiness using (Job)
open import AoP.TardinessBound using (charge)
open import AoP.ScheduleDuration using (total)
open import AoP.Permutations using (Insert; front; later)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.NatOrder using (_≤_; rid; chain; compare)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- §10.3. Choose a job to execute last, not the job with least penalty
-- if started now. All candidates are compared at the same finish time
-- t. In a tie keep the earlier input occurrence. The insertion witness
-- lets the scheduler remove exactly that occurrence, without job equality.
record Pick (t : Nat) (jobs : List Job) : Set where
  constructor picked
  field
    last : Job
    others : List Job
    restore : Insert last others jobs
    cheapest : ∀ j → j ∈ jobs → charge last t ≤ charge j t

pick : ∀ t j js → Pick t (j ∷ js)
pick t j [] = picked j [] front λ { _ here → rid _ ; _ (there ()) }
pick t j (k ∷ ks) with pick t k ks
... | picked z zs restore cheap with compare (charge j t) (charge z t)
...   | inl le = picked j (k ∷ ks) front λ where
      _ here → rid _
      x (there p) → chain le (cheap x p)
...   | inr ge = picked z (j ∷ zs) (later restore) λ where
      _ here → ge
      x (there p) → cheap x p

pick-last : ∀ j js → Pick (total (j ∷ js)) (j ∷ js)
pick-last j js = pick (total (j ∷ js)) j js
