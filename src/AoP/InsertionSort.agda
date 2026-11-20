{-# OPTIONS --safe --without-K #-}
module AoP.InsertionSort where

open import AoP.Prelude
open import AoP.Selection
open import AoP.SelectionSort using (Perm; finish; emit; Sorted; nil; cons; Result)
open import AoP.NatOrder using (_≤_; compare)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 6.30. Fold from the right, inserting each key into a sorted
-- suffix. Remove read backwards is the relation `add`: deleting the new
-- occurrence from the result must recover the old suffix exactly.
lower-add : ∀ {a k xs ys} → k ≤ a → Lower k xs → Remove a ys xs → Lower k ys
lower-add ka lb head = below ka lb
lower-add ka (below kx lb) (past p) = below kx (lower-add ka lb p)

-- The fusion guard: if the output of add is ordered, the input already
-- was ordered. The reverse inclusion simply forgets this extra guard.
ordered-delete : ∀ {a xs ys} → Remove a ys xs → Sorted ys → Sorted xs
ordered-delete head (cons lb sorted) = sorted
ordered-delete (past p) (cons lb sorted) = cons (snd (old-bound p lb)) (ordered-delete p sorted)
  where
  old-bound = AoP.SelectionSort.remove-bound

insert : ∀ a xs → Sorted xs → Σ _ λ ys → Remove a ys xs × Sorted ys
insert a [] nil = (a ∷ []) , head , cons empty nil
insert a (x ∷ xs) (cons lb sorted) with compare a x
... | inl ax = _ , head , cons (below ax (weaken ax lb)) (cons lb sorted)
... | inr xa with insert a xs sorted
...   | ys , rem , ok = _ , past rem , cons (lower-add xa lb rem) ok

-- Carry a permutation of the suffix through one insertion. Passing an
-- emitted key moves its removal one place deeper in the original input.
carry : ∀ {a xs ys zs} → Remove a zs ys → Perm xs ys → Perm (a ∷ xs) zs
carry head perm = emit head perm
carry (past p) (emit r perm) = emit (past r) (carry p perm)

sort : ∀ xs → Result xs
sort [] = [] , finish , nil
sort (a ∷ xs) with sort xs
... | ys , perm , ok with insert a ys ok
...   | zs , rem , sorted = zs , carry rem perm , sorted

example : fst (sort (2 ∷ 3 ∷ 1 ∷ 2 ∷ [])) ≡ 1 ∷ 2 ∷ 2 ∷ 3 ∷ []
example = refl
