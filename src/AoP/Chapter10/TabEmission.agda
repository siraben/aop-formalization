{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TabEmission where

open import Agda.Builtin.Nat using (Nat; suc)
open import AoP.Common.Prelude
open import AoP.Chapter10.Detab
open import AoP.Chapter10.Entab
open import AoP.Chapter10.TabCountdown using (module Count)
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter01.Snoc using (_▻_)
open import AoP.Chapter04.Complement using (⊥)

-- §10.2: project a dependent buffer onto the two fields that affect the
-- next encoding decision. The countdown can now predict the actual
-- code emitted by a whole run, not merely how many blanks it represents.
module Emission {A : Set} (n : Nat) where
  open Expand {A} n
  open Encode {A} n
  open Count
  State = Text × Nat

  view : ∀ {s} → Buffer s → State
  view b = Buffer.code b , Buffer.pending b

  tick : State → State
  tick (xs , k) with test k (position (detab xs))
  ... | same _ = (xs ▻ tab) , 0
  ... | different _ = xs , suc k

  simulates : ∀ {s} (b : Buffer s) → view (add-space b) ≡ tick (view b)
  simulates (buf xs k p) with test k (position (detab xs))
  ... | same refl = refl
  ... | different _ = refl

  absurd : ∀ {T : Set} → ⊥ → T
  absurd ()

  module Prefix (xs : Text) where
    m = position (detab xs)
    wait : Nat → State
    wait k = xs , k
    emit : State
    emit = (xs ▻ tab) , 0

    at : tick (wait m) ≡ emit
    at with test m m
    ... | same _ = refl
    ... | different no = absurd (no refl)

    early : ∀ k → suc k ≤ m → tick (wait k) ≡ wait (suc k)
    early k lt with test k m
    ... | different _ = refl
    ... | same eq = absurd (bad k m eq lt)
      where
      bad : ∀ k j → k ≡ j → suc k ≤ j → ⊥
      bad k .k refl = irreflexive k

    open Trace tick wait emit m at early public
