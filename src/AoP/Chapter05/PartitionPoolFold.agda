{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PartitionPoolFold where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph using (_∷⁺_)
open import AoP.Chapter05.PartitionLayerInverse using (module Law)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Appendix.ListProduct using (collect; locate)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (concat)
open import AoP.Chapter04.Relations using (nil; cons)

-- §5.6. Transpose the new/glue layer by listing its possible outputs.
-- New applies even to the empty tail partition. Glue needs a first
-- block to extend, so on empty input the row contains only one entry.
module Derive (A : Set) where
  open Law A hiding (sound)
  row : A → Blocks → List Blocks
  row x [] = ((x ∷⁺ []) ∷ []) ∷ []
  row x ((y ∷⁺ ys) ∷ ps) = ((x ∷⁺ []) ∷ (y ∷⁺ ys) ∷ ps) ∷ ((x ∷⁺ (y ∷ ys)) ∷ ps) ∷ []
  read : ∀ x ps {p} → p ∈ row x ps → Step p (x , ps)
  read x [] here = new
  read x [] (there ())
  read x ((y ∷⁺ ys) ∷ ps) here = new
  read x ((y ∷⁺ ys) ∷ ps) (there here) = glue
  read x ((y ∷⁺ ys) ∷ ps) (there (there ()))
  write : ∀ {x ps p} → Step p (x , ps) → p ∈ row x ps
  write {ps = []} new = here
  write {ps = _ ∷ _} new = here
  write glue = there here
  pool : List A → List Blocks
  pool [] = [] ∷ []
  pool (x ∷ xs) = concat (map (row x) (pool xs))
  -- Flattening the rows implements union. A membership witness in
  -- the flattened result recovers both the old partition and its step.
  sound : ∀ xs {p} → p ∈ pool xs → Partition p xs
  sound [] here = nil refl
  sound [] (there ())
  sound (x ∷ xs) h with locate (row x) (pool xs) h
  ... | ps , old , choice = cons (read x ps choice) (sound xs old)
  complete-pool : ∀ {xs p} → Partition p xs → p ∈ pool xs
  complete-pool (nil refl) = here
  complete-pool (cons {x} s h) = collect (row x) (complete-pool h) (write s)
