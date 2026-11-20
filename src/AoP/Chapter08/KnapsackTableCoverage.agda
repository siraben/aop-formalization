{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.KnapsackTableCoverage where

open import AoP.Common.Prelude
open import AoP.Chapter08.KnapsackFrontier using (Summary; _≼_; module Sweep)
open import AoP.Chapter08.KnapsackGuardStep using (Next; match; skip)
open import AoP.Chapter08.KnapsackSortedTable using (module Table)
open import AoP.Chapter08.KnapsackStreamLaw using (module Law)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter08.Thinning using (Thin)
open import AoP.Common.NatOrder using (chain; rid)
open import Agda.Builtin.Nat using (Nat)

-- A legal history starts with the empty pack. The step witness records
-- taking or skipping each item, including the capacity test on a take.
module Search (cap : Nat) where
  open Table cap
  data Run : List Summary → Summary → Set where
    empty : Run [] (0 , 0)
    more : ∀ {i is p r} → Run is p → Next cap i p r → Run (i ∷ is) r

  sound : ∀ is {p} → p ∈ table is → Run is p
  sound [] here = empty
  sound (i ∷ is) m with Law.decode cap i (table is) (Thin.subset (Sweep.correct (stream i (table is))) m)
  ... | q , from , next = more (sound is from) next

  cover : ∀ {is r} → Run is r → Σ Summary λ p → (p ∈ table is) × (p ≼ r)
  cover empty = _ , here , rid 0 , rid 0
  cover (more {i} {is} run next) with cover run
  ... | p , mem , dom with match cap i dom next
  ...   | s , legal , improves with Thin.cover (Sweep.correct (stream i (table is))) s (Law.encode cap i (table is) (p , mem , legal))
  ...     | a , kept , light , rich = a , kept , chain light (fst improves) , chain (snd improves) rich

  all-skip : ∀ is → Run is (0 , 0)
  all-skip [] = empty
  all-skip (i ∷ is) = more (all-skip is) skip
