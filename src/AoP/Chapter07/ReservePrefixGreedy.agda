{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ReservePrefixGreedy where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; Fold)
open import AoP.Chapter07.GreedyFold using (module Lists)
open import AoP.Chapter08.Thinning using (Min)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter07.SignedSegment using (_≤_; cmp; rid; chain; add; mono)
open import Agda.Builtin.Int using (Int; pos; negsuc)

-- Exercise 7.55. Every prefix sum is either zero (stop now) or the
-- current transaction plus a prefix sum of the remaining transactions.
-- Taking the entire tail prefix is allowed. Use exactly this relational
-- algebra for both greedy applications, reversing only the score order.
Seed : Int → Set
Seed x = x ≡ pos 0
data Next : Int ← (Int × Int) where
  stop : ∀ {t x} → Next (pos 0) (t , x)
  more : ∀ {t x} → Next (add t x) (t , x)

module Scan (R : Int → Int → Set) (unit : ∀ x → R x x)
            (join : ∀ {x y z} → R x y → R y z → R x z)
            (cmpR : ∀ x y → R x y ⊎ R y x)
            (shift : ∀ t {x y} → R x y → R (add t x) (add t y)) where
  match : ∀ {t x y z} → R x y → Next z (t , y) → Σ Int λ w → Next w (t , x) × R w z
  match xy stop = _ , stop , unit _
  match {t} xy more = _ , more , shift t xy
  module G = Lists R join Seed Next match
  run : ∀ ts → Σ Int λ x → G.Greedy x ts
  run [] = pos 0 , G.seed (refl , λ { _ refl → unit _ })
  run (t ∷ ts) with run ts
  ... | x , g with cmpR (pos 0) (add t x)
  ...   | inl p = pos 0 , G.step g (stop , λ { _ stop → unit _ ; _ more → p })
  ...   | inr p = add t x , G.step g (more , λ { _ stop → p ; _ more → unit _ })
  optimum : ∀ ts → Min R (fst (run ts)) (λ x → Fold Seed Next x ts)
  optimum ts = G.optimum (snd (run ts))

module Floor = Scan _≤_ rid chain cmp mono
module Ceiling = Scan (λ x y → y ≤ x) rid (λ p q → chain q p) (λ x y → cmp y x) (λ t {x} {y} → mono t {y} {x})
sample = pos 2 ∷ negsuc 4 ∷ pos 7 ∷ []
low : fst (Floor.run sample) ≡ negsuc 2
low = refl
high : fst (Ceiling.run sample) ≡ pos 4
high = refl
