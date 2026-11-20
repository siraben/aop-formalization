{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.ScheduleAlgebraOrder where

open import AoP.Common.Prelude
open import AoP.Chapter05.Permutations using (Perm)
open import AoP.Chapter10.ScheduleDuration using (total; perm-total)
open import AoP.Chapter10.Tardiness using (Job; penalty)
open import AoP.Chapter01.Trees using (max)
open import AoP.Common.NatOrder using (_≤_; rid; z≤; s≤; weaken)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 10.5. Choose any listing of the prefix bag to compute the
-- final job's completion time. All representatives give the same time,
-- so increasing the prefix cost cannot decrease the new maximum.
private
  below : ∀ a b → b ≤ max a b
  below 0 b = rid b
  below (suc a) 0 = z≤
  below (suc a) (suc b) = s≤ (below a b)
  mono : ∀ {a b} t → a ≤ b → max a t ≤ max b t
  mono {b = b} t z≤ = below b t
  mono 0 (s≤ p) = s≤ p
  mono (suc t) (s≤ p) = s≤ (mono t p)

extend : Nat → List Job → Job → Nat
extend k jobs j = max k (penalty (total jobs) j)

step : ∀ {a b xs ys} j → a ≤ b → Perm xs ys → extend a xs j ≤ extend b ys j
step j le perm rewrite perm-total perm = mono _ le

base : 0 ≤ 0
base = rid 0
