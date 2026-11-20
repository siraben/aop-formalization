{-# OPTIONS --safe --without-K #-}
module AoP.TeXLoopSound where

open import AoP.Prelude
open import AoP.TeXResidualLoop
open import AoP.TeXPrinterStep using (module Emit)
open import AoP.TeXResidualAccept using (accept)
open import AoP.TeXGridStop using (InCell)
open import AoP.TeXClosestShortest using (scale; numerator)
open import AoP.NatOrder using (_≤_; s≤; z≤)
open import AoP.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- A successful run returns a decimal in its input interval. The
-- separate termination theorem rules out the exhausted branch at TeX width.
module Sound (k : Nat) where
  w = suc k
  Good : Nat → Nat → Result → Set
  Good p q exhausted = 0 ≡ 0
  Good p q (printed ds) = InCell w (p * scale ds) (q * scale ds) (numerator ds)
  sound : ∀ fuel p j (b : suc j ≤ w) → Good p (suc j) (Loop.run k fuel p j b)
  sound fuel 0 j b = z≤ , s≤ z≤
  sound 0 (suc p) j b = refl
  sound (suc fuel) (suc p) j b = lift r (sound fuel E.low (pred E.high) nb)
    where module E = Emit k j 0 (suc p) b
          nb = next-bound k E.high E.next-high
          r = Loop.run k fuel E.low (pred E.high) nb
          lift : ∀ s → Good E.low (suc (pred E.high)) s → Good (suc p) (suc j) (prepend E.letter s)
          lift exhausted h = refl
          lift (printed ds) h = accept w (suc p) (suc j) E.d (scale ds) (numerator ds) E.exact (transport (nonzero E.high (fst E.next-high)) h)
            where transport : ∀ {a c} → a ≡ c → Good E.low c (printed ds) → Good E.low a (printed ds)
                  transport refl h = h
