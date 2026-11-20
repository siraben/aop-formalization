{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.BracketFrontierCoverage where

open import AoP.Common.Prelude
open import AoP.Chapter09.BracketSpineDominance using (module Law)
open import AoP.Chapter09.BracketSpineDecision using (module Check)
open import AoP.Chapter09.BracketFrontier using (module Build)
open import AoP.Chapter09.BracketSpine using (options; occurs)
open import AoP.Chapter09.BracketEnumeration using (enumerate; placed)
open import AoP.Chapter01.Trees using (Tree; tip)
open import AoP.Appendix.ListProduct using (locate; collect)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter08.Thinning using (Thin)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import Agda.Builtin.Nat using (Nat)

module Cover {A S : Set} (atom : A → S) (combine : S → S → S) (charge : S → S → Nat)
             (eq? : ∀ (x y : S) → Dec (x ≡ y)) where
  open Build atom combine charge eq?
  open Law atom combine charge
  open Check atom combine charge eq? using (self; compose; module Thin)
  -- Follow each exhaustive insertion through the thinned fold. The
  -- previous survivor simulates the insertion. Thin.cover then supplies
  -- a new survivor; transitivity composes the two dominance witnesses.
  cover : ∀ a xs {t} → t ∈ enumerate (a ∷ xs) → Σ (Tree A) λ w → (w ∈ pool a xs) × Spine w t
  cover a [] here = tip a , here , self _
  cover a [] (there ())
  cover a (b ∷ xs) m with locate (options a) (enumerate (b ∷ xs)) m
  ... | u , old , pos with cover b xs old
  ...   | v , kept , dom with simulate dom (placed a u pos)
  ...     | z , i , better with Thin.cover (Thin.correct (expand a (pool b xs))) z (collect (options a) kept (occurs i))
  ...       | w , mem , p = w , mem , compose p better
