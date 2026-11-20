{-# OPTIONS --safe --without-K #-}
module AoP.KnapsackStreamLaw where

open import AoP.Prelude
open import AoP.KnapsackFrontier using (Summary; _⊞_)
open import AoP.KnapsackSortedBranches using (Desc; module Branch)
open import AoP.KnapsackSortedTable using (module Table)
open import AoP.KnapsackMerge using (merge; retain; source)
open import AoP.KnapsackGuardStep using (Next; take; skip)
open import AoP.SortedFilter using (module Restrict)
open import AoP.Subsequences using (_∈_; preimage; image)
open import AoP.Horner using (map)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- A row of the merged table still has a take/skip witness even after
-- filtering and sorting. Conversely every enabled extension appears.
module Law (cap : Nat) (i : Summary) (xs : List Summary) where
  open Branch cap i using (Fits; test) renaming (take to takes)
  open Restrict Desc Fits test using (sound; complete)
  tr = snd (merge (takes xs) xs)
  Runs : Summary → Set
  Runs r = Σ Summary λ p → (p ∈ xs) × Next cap i p r
  decode : ∀ {r} → r ∈ Table.stream cap i xs → Runs r
  decode m with source tr m
  ... | inr p = _ , p , skip
  ... | inl q with sound (map (i ⊞_) xs) _ q
  ...   | elem , fits with preimage (i ⊞_) xs elem
  ...     | p , mem , refl = p , mem , take fits
  encode : ∀ {r} → Runs r → r ∈ Table.stream cap i xs
  encode (p , member , skip) = retain tr (inr member)
  encode (p , member , take fits) = retain tr (inl (complete (map (i ⊞_) xs) _ (image (i ⊞_) member) fits))
