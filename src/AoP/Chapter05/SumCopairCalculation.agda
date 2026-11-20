{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.SumCopairCalculation where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Relations
open import AoP.Chapter05.RelationalSums using (_⊕_; left; right)
open import AoP.Chapter05.CopairCancellation using (copair)
open import AoP.Chapter04.Shunting using (graph)

-- §5.3 (5.10). The inner relation supplies a branch output. The
-- injection tags it, and copairing chooses which composite to use.
-- This specification derives exactly the tag-preserving inductive lift.
module Branches {A B C D : Set} (R : B ← A) (S : D ← C) where
  cases : (B ⊎ D) ← (A ⊎ C)
  cases = copair (graph inl ∘ R) (graph inr ∘ S)
  tagged : cases ⊆ R ⊕ S
  tagged {a = inl a} (_ , refl , r) = left r
  tagged {a = inr c} (_ , refl , s) = right s
  expand : R ⊕ S ⊆ cases
  expand (left r) = _ , refl , r
  expand (right s) = _ , refl , s
