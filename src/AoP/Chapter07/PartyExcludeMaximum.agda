{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.PartyExcludeMaximum where

open import AoP.Common.Prelude
open import AoP.Chapter07.PartyChoiceOrder using (module Law)
import AoP.Chapter07.PartyConcatOrder as Scores
import AoP.Chapter07.PartyIncludeExclude as Joint
open import AoP.Chapter05.ListMeet using (Align; nil; cons)
open import AoP.Chapter01.Naturality using (concat)
open import AoP.Common.NatOrder using (compare; rid)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 7.43. For a supervisor who stays home, independently choose
-- a best alternative for each report and concatenate the resulting lists.
module Solve {E : Set} (rating : E → Nat) where
  open Scores.Law rating
  open Law R
  open Joint.Build rating using (Candidates; build; include)
  Best : Pair → Set
  Best p = Σ (List E) λ xs → Choose xs p × (∀ {ys} → Choose ys p → R xs ys)
  pick : ∀ p → Best p
  pick (a , b) with compare (score b) (score a)
  ... | inl p = a , left a b , λ { (left _ _) → rid _ ; (right _ _) → p }
  ... | inr q = b , right a b , λ { (left _ _) → q ; (right _ _) → rid _ }

  choices : ∀ ps → Σ (List (List E)) λ xs → Align Choose xs ps ×
            (∀ {ys} → Align Choose ys ps → Align R xs ys)
  choices [] = [] , nil , λ { nil → nil }
  choices (p ∷ ps) with pick p | choices ps
  ... | x , legal , best | xs , aligned , bound = (x ∷ xs) , cons legal aligned ,
    λ { (cons r rs) → cons (best r) (bound rs) }

  maximum : ∀ e ps → Σ Pair λ p → Candidates e ps p × (∀ {q} → Candidates e ps q → Better p q)
  maximum e ps with choices ps
  ... | xs , aligned , bound = (include e ps , concat xs) , build xs aligned ,
    λ { (build ys legal) → rid _ , flatten (bound legal) }
