{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.ModularRefinement where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
private variable A B C : Set

-- Exercise 4.5 in Rel. Suppose an R-edge also factors through S and
-- T. Restrict the T-edge to intermediate points connected back through
-- S to an R-output. The same factorization witnesses the restriction.
module Restrict (R : C ← A) (S : C ← B) (T : B ← A) where
  narrowed = (S ˘ ∘ R) ⊓ T

  introduce : R ⊓ (S ∘ T) ⊆ R ⊓ (S ∘ narrowed)
  introduce {c} (r , (b , s , t)) = r , b , s , (c , s , r) , t

  forget : R ⊓ (S ∘ narrowed) ⊆ R ⊓ (S ∘ T)
  forget (r , (b , s , back-edge , t)) = r , b , s , t

-- Exercise 4.6. Any edge supplies its own forward-backward-forward
-- path. No hypothesis of symmetry or transitivity is needed.
zigzag : (R : B ← A) → R ⊆ R ∘ R ˘ ∘ R
zigzag R {b} {a} r = a , r , b , r , r
