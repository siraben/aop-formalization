{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PartitionFlatten where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_; module Layout)
open import AoP.Chapter08.LineBreaks using (module Breaks)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)

-- Exercise 5.26. Every block must be nonempty; the outer list may be
-- empty. A candidate is a partition exactly when concatenating its
-- blocks recovers the input. Peel off a singleton first block with new,
-- or the first item of a longer block with glue, to reconstruct a run.
module Law (A : Set) where
  open Layout {Word = A} (λ _ → 0) 0
  open Breaks {Word = A} (λ _ → 0) 0

  derive : ∀ ls w ws → Partition w (ws ++ flatten ls) ((w ∷⁺ ws) ∷⁺ ls)
  derive [] w [] = single w
  derive ((v ∷⁺ vs) ∷ ls) w [] = break-before-tail w (derive ls v vs)
  derive ls w (v ∷ vs) = continue-line w (derive ls v vs)

  blocks : Para → List Line
  blocks (l ∷⁺ ls) = l ∷ ls

  -- Handle the empty input explicitly. On nonempty input reuse the
  -- complete new/glue enumeration already needed for paragraph layout.
  open import AoP.Chapter03.Horner using (map)
  partitions : List A → List (List Line)
  partitions [] = [] ∷ []
  partitions (x ∷ xs) = map blocks (enumerate x xs)

  open import AoP.Chapter05.Subsequences using (image; preimage)
  sound′ : ∀ xs p → p ∈ partitions xs → flatten p ≡ xs
  sound′ [] .[] here = refl
  sound′ [] p (there ())
  sound′ (x ∷ xs) p m with preimage blocks (enumerate x xs) m
  ... | (l ∷⁺ ls) , q , refl = preserves-text (sound x xs q)

  complete′ : ∀ p → p ∈ partitions (flatten p)
  complete′ [] = here
  complete′ ((w ∷⁺ ws) ∷ ls) = image blocks (complete (derive ls w ws))

  recover : ∀ xs p → flatten p ≡ xs → p ∈ partitions xs
  recover .(flatten p) p refl = complete′ p
