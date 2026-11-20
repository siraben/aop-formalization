{-# OPTIONS --safe --without-K #-}
module AoP.LatenessPeakBound where

open import AoP.Prelude
open import AoP.SignedLateness using (Peak; bottom; finite; raise; score; charge)
open import AoP.SignedSegment using (_≤_; cmp; chain)
open import AoP.Polynomial using (inl; inr)
open import AoP.LatenessExchange using (module Limit)
open import AoP.Tardiness using (Job; elapsed)
open import AoP.Snoc using (Snoc; append; ε; _▻_)
open import Agda.Builtin.Int using (Int)

-- A ceiling always admits the empty peak. Raising a peak meets the
-- ceiling precisely when both the old peak and the new job meet it.
Below : Peak → Int → Set
Below bottom k = ⊤
Below (finite p) k = p ≤ k
put : ∀ p q k → Below p k → q ≤ k → Below (raise p q) k
put bottom q k old new = new
put (finite p) q k old new with cmp p q
... | inl _ = new
... | inr _ = old
split : ∀ p q k → Below (raise p q) k → Below p k × (q ≤ k)
split bottom q k ok = tt , ok
split (finite p) q k ok with cmp p q
... | inl le = chain le ok , ok
... | inr ge = ok , chain ge ok

module Bound (k : Int) where
  open Limit k using (Fits; empty; step)
  -- Thread an already processed prefix through the remaining schedule.
  -- Taking ε as prefix identifies the snoc score with jobwise Fits.
  collect : ∀ prefix js → Below (score prefix) k → Fits (elapsed prefix) js → Below (score (append prefix js)) k
  collect p [] old empty = old
  collect p (j ∷ js) old (step ok tail) = collect (p ▻ j) js (put (score p) _ k old ok) tail
  expose : ∀ p js → Below (score (append p js)) k → Below (score p) k × Fits (elapsed p) js
  expose p [] ok = ok , empty
  expose p (j ∷ js) ok with expose (p ▻ j) js ok
  ... | both , rest with split (score p) (charge j (elapsed (p ▻ j))) k both
  ...   | old , meets = old , step meets rest
