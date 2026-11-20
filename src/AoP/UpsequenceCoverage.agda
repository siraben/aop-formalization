{-# OPTIONS --safe --without-K #-}
module AoP.UpsequenceCoverage where

open import AoP.Prelude
open import AoP.UpsequenceFrontier using (frontier; extensions; prune-step)
open import AoP.UpsequenceDominance using (module Law)
open import AoP.UpsequenceExtensions using (intro)
open import AoP.Subsequences using (Subseq; _∈_; here; merge)
open import AoP.Thinning using (Thin)
open import AoP.Relations using (nil; cons)
open import AoP.Refinement using (skip; keep)
open import AoP.Polynomial using (inl; inr)
open import AoP.NatOrder using (_≤_; s≤)
open import Agda.Builtin.Nat using (Nat)
open Law _≤_ using (Ordered; Dominates; reflexive; transitive) renaming (cons to prepend)

Covered : List Nat → List Nat → Set
Covered xs ys = Σ (List Nat) λ zs → (zs ∈ frontier xs) × Dominates zs ys

-- Follow an arbitrary ordered competitor through every pruning step.
-- A retained replacement admits the same next element if taken; after
-- prepending it, the heads agree and the length comparison is preserved.
cover : ∀ {xs ys} → Subseq ys xs → Ordered ys → Covered xs ys
cover (nil refl) ord = [] , here , reflexive []
cover (cons {a} {xs} skip sub) ord with cover sub ord
... | zs , mem , dom with Thin.cover (prune-step a (frontier xs)) zs (merge (extensions a (frontier xs)) (frontier xs) (inr mem))
...   | ws , kept , replaces = ws , kept , transitive ws zs _ replaces dom
cover (cons {a} {xs} keep sub) (prepend ok ord) with cover sub ord
... | zs , mem , (le , admit) with Thin.cover (prune-step a (frontier xs)) (a ∷ zs) (merge (extensions a (frontier xs)) (frontier xs) (inl (intro a (frontier xs) mem (admit a ok))))
...   | ws , kept , replaces = ws , kept , transitive ws (a ∷ zs) _ replaces (s≤ le , λ _ p → p)
