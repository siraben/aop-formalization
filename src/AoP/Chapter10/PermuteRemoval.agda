{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.PermuteRemoval where

open import AoP.Common.Prelude
open import AoP.Chapter05.Permutations
private variable A : Set

-- §10.3. A last-job choice removes an occurrence from the input bag,
-- but a competing schedule presents those jobs in a different order.
-- Transport that particular removal through the permutation. This does
-- not require decidable equality, even when two jobs have equal fields.
-- First commute two adjacent insertions, remembering where both went.
commute : ∀ {a b : A} {xs ys zs} → Insert a xs ys → Insert b ys zs →
          Σ _ λ ws → Insert b xs ws × Insert a ws zs
commute p front = _ , front , later p
commute front (later q) = _ , q , front
commute (later p) (later q) with commute p q
... | ws , r , s = _ , later r , later s

remove-permuted : ∀ {a : A} {xs ys zs} → Insert a xs ys → Perm ys zs →
                  Σ _ λ ws → Perm xs ws × Insert a ws zs
remove-permuted front (insert p i) = _ , p , i
remove-permuted (later r) (insert p i) with remove-permuted r p
... | ws , p′ , j with commute j i
...   | vs , k , l = vs , insert p′ k , l
