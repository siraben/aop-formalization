{-# OPTIONS --safe --without-K #-}
module AoP.ObjectiveThinningExample where

open import AoP.Prelude
open import AoP.ObjectiveThinning using (module Compare)
open import AoP.NatOrder using (_≤_; rid; chain; s≤; z≤)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 9.4. Two decompositions have multiple feasible outcomes.
-- Thinning compares the attainable minima, not arbitrary samples:
-- choosing the expensive result 9 for left would reverse the ranking.
data Decomp : Set where left right : Decomp
data Outcome : Nat → Decomp → Set where
  l2 : Outcome 2 left
  l9 : Outcome 9 left
  r4 : Outcome 4 right
  r6 : Outcome 6 right
open Compare Outcome _≤_ chain
l-best : M 2 left
l-best = l2 , λ { _ l2 → rid 2 ; _ l9 → s≤ (s≤ z≤) }
r-best : M 4 right
r-best = r4 , λ { _ r4 → rid 4 ; _ r6 → s≤ (s≤ (s≤ (s≤ z≤))) }
rank : C left right
rank = 2 , l-best , 4 , s≤ (s≤ z≤) , r-best
matched : fst (replay (right , r6 , rank)) ≡ 2
matched = refl
-- No comparison in the opposite direction: it would imply that the
-- minimum on the right beats 2, contradicting both right outcomes.
reverse-impossible : C right left → ⊥
reverse-impossible (b , (ok , _) , a , bound , (_ , best)) with chain bound (best 2 l2) | ok
... | s≤ (s≤ ()) | r4
... | s≤ (s≤ ()) | r6
