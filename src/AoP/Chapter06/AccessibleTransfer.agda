{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.AccessibleTransfer where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter06.Inductive using (Acc; acc)

-- Exercise 6.13. Replace the first of two consecutive R steps by
-- an S step, keeping the endpoint of the pair. Induct on S at the
-- source x with the strengthened claim: every R-child y is accessible.
module Transfer {A : Set} (R S : A ← A) (replace : R ∘ R ⊆ R ∘ S) where
  children : ∀ {x} → Acc S x → ∀ y → R y x → Acc R y
  children (acc down) y first = acc λ z second →
    let w , last , initial = replace (y , second , first)
    in children (down w initial) z last

  well-founded : (∀ x → Acc S x) → ∀ x → Acc R x
  well-founded wf x = acc (children (wf x))
