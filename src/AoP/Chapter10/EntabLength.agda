{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.EntabLength where

open import AoP.Common.Prelude
open import AoP.Chapter10.Detab
open import AoP.Chapter10.Entab
open import AoP.Chapter10.TabFree
open import AoP.Chapter01.Snoc using (ε; _▻_)
open import AoP.Common.NatOrder using (_≤_; rid; chain; s≤; weaken)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §10.2. Round-trip correctness alone would permit an encoder that never
-- emits a tab. As a first bound on encoded length, charge one character
-- per pending space. Flushing then costs exactly what was charged;
-- replacing a whole run by a tab costs no more than that charge.
module Bound {A : Set} (n : Nat) where
  open Expand {A} n
  open Image {A} n
  open Encode {A} n

  len : Text → Nat
  len ε = 0
  len (s ▻ _) = suc (len s)

  size : ∀ {s} → Buffer s → Nat
  size (buf xs k _) = len (blanks xs k)

  grows : ∀ xs k → len xs ≤ len (blanks xs k)
  grows xs zero = rid _
  grows xs (suc k) = chain (weaken (rid _)) (grows (xs ▻ blank) k)

  space-bound : ∀ {s} (b : Buffer s) → size (add-space b) ≤ suc (size b)
  space-bound (buf xs k inv) with test k (position (detab xs))
  ... | same refl = s≤ (grows xs (position (detab xs)))
  ... | different _ rewrite snoc-blanks xs k = rid _

  size-flush : ∀ {s} (b : Buffer s) → len (fst (flush b)) ≡ size b
  size-flush (buf _ _ _) = refl

  bound : ∀ {s} (p : Plain s) → size (encode p) ≤ len s
  bound empty = rid 0
  bound (space p) = chain (space-bound (encode p)) (s≤ (bound p))
  bound (line p) = s≤ (bound p)
  bound (char a p) = s≤ (bound p)

  no-longer : ∀ {s} (p : Plain s) → len (fst (entab p)) ≤ len s
  no-longer p = bound p
