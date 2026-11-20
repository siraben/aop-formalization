{-# OPTIONS --safe --without-K #-}
module AoP.PartyIncludeExclude where

open import AoP.Prelude
open import AoP.PartyChoiceOrder using (module Law)
import AoP.PartyConcatOrder as Scores
open import AoP.ListMeet using (Align; nil; cons)
open import AoP.Horner using (map)
open import AoP.Naturality using (concat)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 7.43. Include the supervisor by taking every report's
-- excluded-root list. Excluding the supervisor permits either choice
-- for each report. Match both results in the *same* improved pair.
module Build {E : Set} (rating : E → Nat) where
  open Scores.Law rating
  open Law R
  include : E → List Pair → List E
  include e ps = e ∷ concat (map snd ps)
  seconds : ∀ {ps qs} → Align Better qs ps → Align R (map snd qs) (map snd ps)
  seconds nil = nil
  seconds (cons r rs) = cons (snd r) (seconds rs)
  include-mono : ∀ e {ps qs} → Align Better qs ps → R (include e qs) (include e ps)
  include-mono e {ps} {qs} improves = prepend e {concat (map snd ps)} {concat (map snd qs)} (flatten (seconds improves))

  data Candidates (e : E) (ps : List Pair) : Pair → Set where
    build : ∀ xs → Align Choose xs ps → Candidates e ps (include e ps , concat xs)
  improve : ∀ e {ps qs old} → Align Better qs ps → Candidates e ps old →
            Σ Pair λ new → Candidates e qs new × Better new old
  improve e improves (build xs picks) with forest improves picks
  ... | ys , choices , bounds = _ , build ys choices , include-mono e improves , flatten bounds
