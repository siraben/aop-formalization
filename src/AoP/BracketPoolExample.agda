{-# OPTIONS --safe --without-K #-}
module AoP.BracketPoolExample where

open import AoP.Prelude
open import AoP.BracketFrontier using (module Build)
open import AoP.BracketEnumeration using (enumerate)
open import AoP.ConversionCost using (len)
open import AoP.Polynomial using (inl)
open import Agda.Builtin.Nat using (Nat)

-- Four leaves of equal size, with one unit charged per binary node.
-- All five bracketings cost three. Their left spines have one, two,
-- or three forks; right subtrees of equal cost and size may be merged.
-- The whole-pool comparison finds replacements across other depths.
module Pool = Build (λ (_ : Nat) → tt) (λ _ _ → tt) (λ _ _ → 1) (λ _ _ → inl refl)

exhaustive-count : len (enumerate (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) ≡ 5
exhaustive-count = refl
survivor-count : len (Pool.pool 1 (2 ∷ 3 ∷ 4 ∷ [])) ≡ 4
survivor-count = refl
