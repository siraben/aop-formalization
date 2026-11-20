{-# OPTIONS --safe --without-K #-}
module AoP.ReserveGreedyClip where

open import AoP.Prelude
open import AoP.ReservePrefixGreedy using (module Floor; module Ceiling)
open import AoP.ReserveClipping using (stock; space)
open import AoP.SignedSegment using (cmp; add; _≤_; pp; np)
open import AoP.NatOrder using (z≤)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Int using (pos; negsuc)

-- Keeping the empty prefix can change the signed winner to zero, but
-- leaves the corresponding natural requirement unchanged: the losing
-- candidate was already on the side whose clipped value is zero.
private
  enough : ∀ x → pos 0 ≤ x → 0 ≡ stock x
  enough (pos _) _ = refl
  room : ∀ x → x ≤ pos 0 → 0 ≡ space x
  room (pos _) (pp z≤) = refl
  room (negsuc _) _ = refl

floor-step : ∀ t ts → stock (fst (Floor.run (t ∷ ts))) ≡ stock (add t (fst (Floor.run ts)))
floor-step t ts with Floor.run ts
... | x , g with cmp (pos 0) (add t x)
...   | inl le = enough (add t x) le
...   | inr ge = refl

ceiling-step : ∀ t ts → space (fst (Ceiling.run (t ∷ ts))) ≡ space (add t (fst (Ceiling.run ts)))
ceiling-step t ts with Ceiling.run ts
... | x , g with cmp (add t x) (pos 0)
...   | inl le = room (add t x) le
...   | inr ge = refl
