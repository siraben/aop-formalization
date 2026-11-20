{-# OPTIONS --safe --without-K #-}
module AoP.IndexedBranches where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 3.44. A node supplies a child for each index of type A.
-- For fixed A the layer functor sends X to A + (A → X). Recursion
-- occurs in the codomain of the child function, so Agda accepts the
-- datatype as strictly positive even for infinitely many branches.
data Tree (A : Set) : Set where
  tip : A → Tree A
  node : (A → Tree A) → Tree A

fold : ∀ {A X : Set} → (A → X) → ((A → X) → X) → Tree A → X
fold leaf branch (tip a) = leaf a
fold leaf branch (node children) = branch (λ i → fold leaf branch (children i))

-- One child per natural number. Following branch 3 reaches the tip 4.
example : Tree Nat
example = node (λ n → tip (suc n))

third : fold (λ a → a) (λ children → children 3) example ≡ 4
third = refl
