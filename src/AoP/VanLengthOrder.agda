{-# OPTIONS --safe --without-K #-}
module AoP.VanLengthOrder where

open import AoP.Prelude
open import AoP.ConversionCost using (len)
open import AoP.NatOrder using (_≤_; s≤; rid)
open import AoP.Reserves using (deposit)
open import AoP.ReserveTransfer using (Executes; sufficient; least)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (_+_)

-- Exercise 7.52 and (7.14). Prepending a block adds one to each
-- partition length, regardless of the contents of the new blocks.
cons-order : ∀ {A : Set} (a b : A) xs ys → len ys ≤ len xs → len (b ∷ ys) ≤ len (a ∷ xs)
cons-order a b xs ys = s≤

-- Why (7.15) fails: split three +4 deposits as 4 | 44 or 44 | 4.
-- The partitions tie in length. Prepending one more deposit to the
-- first block succeeds for 4 | 44 and fails for 44 | 4 at capacity 10.
one = deposit 4 ∷ []
two = deposit 4 ∷ one
three = deposit 4 ∷ two

tie : len (one ∷ two ∷ []) ≡ len (two ∷ one ∷ [])
tie = refl
fits : Executes two 0 10
fits = sufficient two 0 10 (AoP.NatOrder.z≤ , s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ AoP.NatOrder.z≤))))))))

overflows : ∀ r s → r + s ≡ 10 → Executes three r s → ⊥
overflows r s eq run with least run
... | bound rewrite eq with bound
...   | s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ ())))))))))
