{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.KnapsackGuardStep where

open import AoP.Common.Prelude
open import AoP.Chapter08.KnapsackFrontier using (Summary; weight; value; _⊞_; _≼_; extend)
open import AoP.Common.NatOrder using (_≤_; chain; rid; z≤; s≤)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)

-- §8.4. Guard the take branch by the weight *after* adding the
-- item; skipping is always allowed on the feasible frontier.
data Next (cap : Nat) (i p : Summary) : Summary → Set where
  take : weight (i ⊞ p) ≤ cap → Next cap i p (i ⊞ p)
  skip : Next cap i p p

match : ∀ cap i {p q r} → p ≼ q → Next cap i q r → Σ Summary λ s → Next cap i p s × (s ≼ r)
match cap i {p} {q} dom (take fits) with extend i {p} {q} dom
... | light , rich = _ , take (chain light fits) , light , rich
match cap i dom skip = _ , skip , dom

-- Capacity 3. The best current value is 5 at weight 3, but keeping
-- only that pack loses the weight-1 pack worth 4. The next item has
-- weight 2 and value 3: from the lighter pack it gives value 7.
light heavy item : Summary
light = 1 , 4
heavy = 3 , 5
item = 2 , 3
initial-value : value light ≤ value heavy
initial-value = s≤ (s≤ (s≤ (s≤ z≤)))
legal : Next 3 item light (3 , 7)
legal = take (rid 3)
no-value-match : ∀ {s} → Next 3 item heavy s → 7 ≤ value s → ⊥
no-value-match (take (s≤ (s≤ (s≤ ())))) _
no-value-match skip (s≤ (s≤ (s≤ (s≤ (s≤ ())))))
