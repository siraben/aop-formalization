{-# OPTIONS --safe --without-K #-}
module AoP.InsertionGapExample where

open import AoP.Prelude
open import AoP.Permutations using (places; Insert; front; later)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 6.30. Inserting 2 into the sorted suffix [1,2] has
-- three legal gaps. The order guard rejects the first. The other
-- two give the same list but identify different occurrences of 2.
suffix : List Nat
suffix = 1 ∷ 2 ∷ []
sorted-output = 1 ∷ 2 ∷ 2 ∷ []
all-gaps : places 2 suffix ≡ (2 ∷ 1 ∷ 2 ∷ []) ∷ sorted-output ∷ sorted-output ∷ []
all-gaps = refl
before-equal after-equal : Insert 2 suffix sorted-output
before-equal = later front
after-equal = later (later front)

open import AoP.SelectionSort using (Sorted; cons)
open import AoP.Selection using (below; empty)
open import AoP.NatOrder using (s≤; z≤; rid)
open import AoP.Complement using (⊥)
rejected : Sorted (2 ∷ 1 ∷ 2 ∷ []) → ⊥
rejected (cons (below (s≤ ()) _) _)
accepted : Sorted sorted-output
accepted = cons (below (s≤ z≤) (below (s≤ z≤) empty)) (cons (below (rid 2) empty) (cons empty AoP.SelectionSort.nil))
