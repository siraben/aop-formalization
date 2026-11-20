{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXNumeratorBounds where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; chain; compare)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open import AoP.Chapter10.StrictUpperQuotient using (choose; strict)
open import AoP.Chapter10.TeXGridStop using (InCell; module Grid)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Convert the half-open scaled reading interval [L,H) to a closed
-- interval of integer numerators. Then intersect it with [0,cap],
-- the numerators printable at this width. The lower endpoint is
-- ceil(L/w), the upper endpoint min(cap, floor((H-1)/w)).
private
  clash : ∀ {i} {X : Set} → suc i ≤ i → X
  clash {0} ()
  clash {suc i} (s≤ p) = clash p
  split : ∀ i j → (i ≤ j) ⊎ (suc j ≤ i)
  split 0 j = inl z≤
  split (suc i) 0 = inr (s≤ z≤)
  split (suc i) (suc j) with split i j
  ... | inl le = inl (s≤ le)
  ... | inr ge = inr (s≤ ge)

module Range (k L h cap : Nat) where
  w = suc k
  ceil : Nat → Nat
  ceil 0 = 0
  ceil (suc m) = suc (choose k m)
  lower : ∀ m t → m ≤ t * w → ceil m ≤ t
  lower 0 t ok = z≤
  lower (suc m) t ok with split t (choose k m)
  ... | inr ge = ge
  ... | inl le = clash (chain (fst (strict k m)) (chain ok (Arithmetic.scale w le)))
  meets : ∀ m → m ≤ ceil m * w
  meets 0 = z≤
  meets (suc m) = snd (strict k m)
  last = choose k h
  module U = Grid w L (suc h) last (strict k h)
  hi : Nat
  hi with compare cap last
  ... | inl le = cap
  ... | inr ge = last
  Exactly = λ t → InCell w L (suc h) t × (t ≤ cap)
  project : ∀ t → Exactly t → (ceil L ≤ t) × (t ≤ hi)
  project t ((lo , upper) , fits) with compare cap last
  ... | inl le = lower L t lo , fits
  ... | inr ge = lower L t lo , U.dominates t upper
  restore : ∀ t → ceil L ≤ t → t ≤ hi → Exactly t
  restore t lo top with compare cap last
  ... | inl le = (low , upper t (chain top le)) , top
    where low = chain (meets L) (Arithmetic.scale w lo)
          upper : ∀ i → i ≤ last → suc (i * w) ≤ suc h
          upper i p = chain (s≤ (Arithmetic.scale w p)) (fst (strict k h))
  ... | inr ge = (chain (meets L) (Arithmetic.scale w lo) , chain (s≤ (Arithmetic.scale w top)) (fst (strict k h))) , chain top ge
