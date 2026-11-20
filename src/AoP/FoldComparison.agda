{-# OPTIONS --safe --without-K #-}
module AoP.FoldComparison where

-- Exercise 6.7, the general order argument. For an algebra R, let
-- runR X denote R ∘ F X; foldR is the least solution. The premise
-- compares the two steps only at foldS. The calculation makes foldS
-- a prefixpoint for runR, so leastness gives the requested inclusion.
-- Abstracting the hom-order also permits large relation carriers.
open import Agda.Primitive using (Level)

module Law {p e : Level} {P : Set p} (_≤_ : P → P → Set e)
           (trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
           (runR runS : P → P) (foldR foldS : P)
           (leastR : ∀ x → runR x ≤ x → foldR ≤ x)
           (computeS : runS foldS ≤ foldS) where
  compare : runR foldS ≤ runS foldS → foldR ≤ foldS
  compare step = leastR foldS (trans step computeS)
