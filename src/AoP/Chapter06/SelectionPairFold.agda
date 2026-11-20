{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SelectionPairFold where

open import AoP.Common.Prelude
open import AoP.Chapter05.Permutations using (Perm; insert; front; later)
open import AoP.Chapter06.Selection using (Lower; below; empty; weaken)
open import AoP.Common.NatOrder using (_≤_; rid; compare)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- The book's pair-valued selector has only the tail's winning pair
-- available at each step. When the head wins, the returned remainder
-- is the reconstructed tail (old winner followed by old remainder).
Pair = Nat × List Nat
base : Nat → Pair
base a = a , []
step : Nat → Pair → Pair
step a (b , xs) with compare a b
... | inl le = a , b ∷ xs
... | inr ge = b , a ∷ xs
select : Nat → List Nat → Pair
select a [] = base a
select a (b ∷ xs) = step a (select b xs)

Valid : List Nat → Pair → Set
Valid input (b , xs) = Perm input (b ∷ xs) × Lower b xs
base-law : ∀ a → Valid (a ∷ []) (base a)
base-law a = insert AoP.Chapter05.Permutations.empty front , empty
step-law : ∀ a input p → Valid input p → Valid (a ∷ input) (step a p)
step-law a input (b , xs) (perm , bound) with compare a b
... | inl le = insert perm front , below le (weaken le bound)
... | inr ge = insert perm (later front) , below ge bound
correct : ∀ a xs → Valid (a ∷ xs) (select a xs)
correct a [] = base-law a
correct a (b ∷ xs) = step-law a (b ∷ xs) (select b xs) (correct b xs)

-- When 0 wins, the tail [2,1] has already been rearranged by the fold.
example : select 0 (2 ∷ 1 ∷ []) ≡ (0 , 1 ∷ 2 ∷ [])
example = refl
