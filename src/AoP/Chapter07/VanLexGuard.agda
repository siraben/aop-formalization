{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanLexGuard where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
open import AoP.Chapter07.VanExtensionOrder using (module Proof)
open import AoP.Chapter07.VanLexOrder using (module Order)
open import AoP.Chapter07.VanHeadOrder using (module Law)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_; s≤)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 7.57. A guarded extension on a longer head can be matched
-- on a prefix head: truncate the same successful run. No suffix
-- closure is needed for monotonicity of this operation.
module Guard (cap : Nat) where
  open Order Tx
  open Law Tx using (keep)
  open Bank cap
  guarded : ∀ a x xs y ys → Q (x ∷ xs) (y ∷ ys) → Secure (a ∷ y) →
            Secure (a ∷ x) × Q ((a ∷ x) ∷ xs) ((a ∷ y) ∷ ys)
  guarded a x xs y ys q (r , s , run) with Proof.truncate cap (keep a (fst q)) run
  ... | t , short = (r , t , short) , glue a x xs y ys q

-- Same flattened input [1,2,3], but the partition preferred by Q has
-- three blocks instead of two. Q alone does not imply the count order.
module Example where
  open Order Nat
  open Law Nat using (keep; empty)
  left = (1 ∷ []) ∷ (2 ∷ []) ∷ (3 ∷ []) ∷ []
  right = (1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ []
  preferred : Q left right
  preferred = keep 1 empty , λ { (keep _ ()) }
  more : len left ≤ len right → ⊥
  more (s≤ (s≤ ()))
