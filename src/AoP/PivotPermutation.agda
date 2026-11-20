{-# OPTIONS --safe --without-K #-}
module AoP.PivotPermutation where

open import AoP.Prelude
open import AoP.Relations using (_←_; _∘_; _⊆_)
open import AoP.Shunting using (graph)
open import AoP.Permutations using (Perm; insert; front)
open import AoP.PermutationGuard using (module Guard)
open import AoP.QuickPermutation using (append-perm; compose)
open import AoP.Naturality using (_++_)
open import AoP.Subsequences using (_∈_)

-- §6.6. Joining list children around a pivot and then allowing every
-- permutation absorbs arbitrary prior rearrangements of the children.
-- Also the pivot bounds depend only on membership on each side. These
-- two equalities are used separately in the split fusion calculation.
module Pivot {A : Set} where
  open Guard {A} using (identity; forward; backward; perm)
  Triple = List A × (A × List A)
  join : Triple → List A
  join (l , p , r) = l ++ (p ∷ r)

  Fperm : Triple ← Triple
  Fperm (l′ , p′ , r′) (l , p , r) = Perm l l′ × ((p′ ≡ p) × Perm r r′)

  absorb : (perm ∘ graph join) ∘ Fperm ⊆ perm ∘ graph join
  absorb (_ , (_ , q , refl) , l , refl , r) = _ , compose (append-perm l (insert r front)) q , refl

  introduce : perm ∘ graph join ⊆ (perm ∘ graph join) ∘ Fperm
  introduce {a = l , p , r} q = _ , q , identity l , refl , identity r

  module Bounds (R : A ← A) where
    Valid : Triple → Set
    Valid (l , p , r) = (∀ {x} → x ∈ l → R x p) × (∀ {x} → x ∈ r → R p x)

    check : Triple ← Triple
    check y x = (y ≡ x) × Valid x

    push : Fperm ∘ check ⊆ check ∘ Fperm
    push (_ , (l , refl , r) , refl , lo , hi) = _ , (refl , (λ m → lo (backward l m)) , (λ m → hi (backward r m))) , l , refl , r

    pull : check ∘ Fperm ⊆ Fperm ∘ check
    pull (_ , (refl , lo , hi) , l , refl , r) = _ , (l , refl , r) , refl , (λ m → lo (forward l m)) , (λ m → hi (forward r m))
