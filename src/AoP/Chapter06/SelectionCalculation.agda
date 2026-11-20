{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SelectionCalculation where

open import AoP.Common.Prelude
open import AoP.Chapter05.Permutations using (Perm; insert; front)
open import AoP.Chapter06.QuickPermutation using (compose)
open import AoP.Chapter06.PermutationGuard using (module Guard)
open import AoP.Chapter05.Subsequences using (_∈_)
open import AoP.Chapter04.Relations using (_←_)

-- §6.6. Three consecutive relations in the selection calculation,
-- written at their endpoints: permute after guarded cons, introduce
-- a permutation of the tail, then move the guard past that permutation.
module Law {A : Set} (R : A ← A) where
  Bound : A → List A → Set
  Bound a xs = ∀ {b} → b ∈ xs → R a b
  Direct Before After : A → List A → List A → Set
  Direct a xs ys = Bound a xs × Perm (a ∷ xs) ys
  Before a xs ys = Σ (List A) λ zs → Bound a xs × Perm xs zs × Perm (a ∷ zs) ys
  After a xs ys = Σ (List A) λ zs → Perm xs zs × Bound a zs × Perm (a ∷ zs) ys

  introduce : ∀ {a xs ys} → Direct a xs ys → Before a xs ys
  introduce {xs = xs} (ok , p) = xs , ok , Guard.identity xs , p
  collapse : ∀ {a xs ys} → Before a xs ys → Direct a xs ys
  collapse (_ , ok , p , q) = ok , compose (insert p front) q

  slide : ∀ {a xs ys} → Before a xs ys → After a xs ys
  slide (zs , ok , p , q) = zs , p , (λ m → ok (Guard.backward p m)) , q
  unslide : ∀ {a xs ys} → After a xs ys → Before a xs ys
  unslide (zs , p , ok , q) = zs , (λ m → ok (Guard.forward p m)) , p , q
