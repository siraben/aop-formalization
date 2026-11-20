{-# OPTIONS --safe --without-K #-}
module AoP.MinimalThinning where

open import AoP.Prelude
open import AoP.Relations using (_←_)
open import AoP.WellSupported using (Supported; module Cover)
open import AoP.MinimalComparison using (Test)
open import AoP.Thinning using (Pred; Thin; Min; thin)

-- Exercise 8.9. Retain precisely the minimal members. For each input
-- member, 7.31 finds a minimal member below it by restricting the
-- search to its predecessors. That member supplies a coverage witness.
module Law {A : Set} (Q : A ← A) (rr : ∀ a → Q a a)
           (tr : ∀ {a b c} → Q a b → Q b c → Q a c) (support : Supported Q) where
  retain : ∀ (X : Pred A) → Thin Q (λ a → Min (Test Q) a X) X
  retain X = thin fst cover
    where cover : ∀ b → X b → Σ A λ a → Min (Test Q) a X × Q a b
          cover b member with Cover.below Q rr tr support X b member
          ... | a , edge , minimal = a , minimal , edge
