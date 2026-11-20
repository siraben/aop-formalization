{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.UpsequenceSound where

open import AoP.Common.Prelude
open import AoP.Chapter08.UpsequenceFrontier using (frontier; extensions; prune-step)
open import AoP.Chapter08.UpsequenceExtensions using (elim)
open import AoP.Chapter08.UpsequenceDominance using (module Law)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; split; Subseq)
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter08.Thinning using (Thin)
open import AoP.Chapter04.Relations using (nil; cons)
open import AoP.Chapter05.Refinement using (keep; skip)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)
open Law _≤_ using (Ordered) renaming (nil to empty; cons to prepend)

-- Every survivor still denotes a genuine ordered subsequence of the
-- original input. Pruning introduces no candidates; split its subset
-- witness into a take or skip and use the tail invariant in either case.
sound : ∀ xs {ys} → ys ∈ frontier xs → Subseq ys xs × Ordered ys
sound [] here = nil refl , empty
sound [] (there ())
sound (a ∷ xs) m with split (extensions a (frontier xs)) (frontier xs) (Thin.subset (prune-step a (frontier xs)) m)
... | inr old with sound xs old
...   | sub , ord = cons skip sub , ord
sound (a ∷ xs) m | inl new with elim a (frontier xs) new
... | zs , old , ok , refl with sound xs old
...   | sub , ord = cons keep sub , prepend ok ord
