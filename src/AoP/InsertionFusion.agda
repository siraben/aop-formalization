{-# OPTIONS --safe --without-K #-}
module AoP.InsertionFusion where

open import AoP.Prelude
open import AoP.Relations using (_←_; _∘_; _⊆_)
open import AoP.Selection using (Remove)
open import AoP.SelectionSort using (Sorted)
open import AoP.InsertionSort using (ordered-delete)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 6.30. Read add backwards as removing the newly inserted
-- occurrence. The input guard keeps the key fixed and asks that its
-- companion list already be sorted. Guarding only the output yields
-- the same relation: deleting one occurrence preserves sortedness.
add : List Nat ← (Nat × List Nat)
add zs (a , xs) = Remove a zs xs
ordered : List Nat ← List Nat
ordered zs ys = (zs ≡ ys) × Sorted zs
input-ok : (Nat × List Nat) ← (Nat × List Nat)
input-ok u v = (u ≡ v) × Sorted (snd u)

introduce : ordered ∘ add ⊆ ordered ∘ add ∘ input-ok
introduce (ys , (refl , ok) , at) = ys , (refl , ok) , _ , at , refl , ordered-delete at ok
absorb : ordered ∘ add ∘ input-ok ⊆ ordered ∘ add
absorb (ys , test , _ , at , refl , _) = ys , test , at
