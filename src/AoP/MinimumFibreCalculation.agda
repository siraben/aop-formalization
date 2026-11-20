{-# OPTIONS --safe --without-K #-}
module AoP.MinimumFibreCalculation where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Power using (Λ)
open import AoP.Thinning using (Min)

-- §7.1 (7.5–6). S describes the feasible outputs at each input.
-- Minimizing its fibre keeps an edge and tests it against every
-- competitor at that same input. No order axioms are needed here.
module Law {A B : Set} (R : A ← A) (S : A ← B) where
  best : A ← B
  best a b = Min R a (Λ S b)
  expand : best ⊆ S ⊓ (R ／ (S ˘))
  expand (feasible , bound) = feasible , (λ {c} rival → bound c rival)
  collect : S ⊓ (R ／ (S ˘)) ⊆ best
  collect (feasible , bound) = feasible , (λ c rival → bound rival)

  -- The universal property splits a proposed implementation X into
  -- feasibility and optimality; the intermediate point in the
  -- composite is the shared input of the candidate and competitor.
  feasible : ∀ {X} → X ⊆ best → X ⊆ S
  feasible sub edge = fst (sub edge)
  optimal : ∀ {X} → X ⊆ best → X ∘ S ˘ ⊆ R
  optimal sub (b , chosen , rival) = snd (sub chosen) _ rival
  introduce : ∀ {X} → X ⊆ S → X ∘ S ˘ ⊆ R → X ⊆ best
  introduce ok wins edge = ok edge , (λ c rival → wins (_ , edge , rival))

  -- (7.6): restrict comparisons to pairs that share some fibre.
  -- The current input already witnesses co-feasibility, including
  -- when the two outputs are different but tied under R.
  local-best : A ← B
  local-best a b = Min (R ⊓ (S ∘ S ˘)) a (Λ S b)
  localize : best ⊆ local-best
  localize {a} {b} (f , bound) = f , (λ c s → bound c s , (b , f , s))
  forget : local-best ⊆ best
  forget (f , bound) = f , (λ c s → fst (bound c s))
