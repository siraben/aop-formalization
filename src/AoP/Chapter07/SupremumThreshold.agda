{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.SupremumThreshold where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.17. The supremum of X is the least of its upper bounds.
-- The two divisions in the alternative specification say that the
-- upper bounds are exactly the elements above the proposed supremum.
module Law {A : Set} (R : A ← A) (rr : ∀ a → R a a)
           (tr : ∀ {a b c} → R a b → R b c → R a c) (X : A → Set) where
  Upper : A → Set
  Upper u = ∀ x → X x → R x u

  Threshold : A → Set
  Threshold a = (∀ u → R a u → Upper u) × (∀ u → Upper u → R a u)

  characterize : ∀ a → Min R a Upper → Threshold a
  characterize a (upper , least) = (λ u au x member → tr (upper x member) au) , least

  supremum : ∀ a → Threshold a → Min R a Upper
  supremum a (above , least) = above a (rr a) , least
