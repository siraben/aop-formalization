{-# OPTIONS --safe --without-K #-}
module AoP.AccessibleFoldPreimage where

open import AoP.Prelude
open import AoP.Relations using (_←_)
open import AoP.Inductive using (Acc; acc)

-- Corollary 6.3 for containers. A preimage for an algebra output
-- consists of a shape and a family of child values. Recursively find
-- a tree for each child; the branch made from them folds to the parent.
module Law {A : Set} (Shape : Set) (Pos : Shape → Set) where
  Layer : Set → Set
  Layer X = Σ Shape (λ s → Pos s → X)
  data Tree : Set where
    branch : (s : Shape) → (Pos s → Tree) → Tree
  module Algebra (R : A ← Layer A) where
    data Fold : A ← Tree where
      node : ∀ {a s xs ts} → R a (s , xs) → (∀ i → Fold (xs i) (ts i)) → Fold a (branch s ts)
    data Child : A ← A where
      at : ∀ {a s xs} → R a (s , xs) → (i : Pos s) → Child (xs i) a
    module Onto (split : ∀ a → Σ (Layer A) (R a)) where
      preimage : ∀ a → Acc Child a → Σ Tree (Fold a)
      preimage a (acc smaller) with split a
      ... | (s , xs) , edge = assemble (λ i → preimage (xs i) (smaller _ (at edge i)))
        where
          assemble : (kids : ∀ i → Σ Tree (Fold (xs i))) → Σ Tree (Fold a)
          assemble kids = branch s (λ i → fst (kids i)) , node edge (λ i → snd (kids i))
