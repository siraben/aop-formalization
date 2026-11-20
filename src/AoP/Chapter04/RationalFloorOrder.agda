{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.RationalFloorOrder where

open import AoP.Common.Prelude
import AoP.Common.NatOrder as N
import AoP.Chapter07.SignedSegment as Z
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Exercise 4.38. Each proper fraction is compared by its lower cut:
-- the probe m/(s+1) lies below r/(d+1) iff m*(d+1) ≤ r*(s+1).
-- Cut inclusion is transitive even when all denominators differ.
record Fraction : Set where
  constructor frac
  field r d : Nat
        proper : r N.≤ d
open Fraction
Cut : Fraction → Nat → Nat → Set
Cut f m s = m * suc (d f) N.≤ r f * suc s
_⊆_ : Fraction → Fraction → Set
f ⊆ g = ∀ m s → Cut f m s → Cut g m s
zero : Fraction
zero = frac 0 0 N.z≤
least : ∀ f → zero ⊆ f
least f 0 s p = N.z≤
least f (suc m) s ()

record Rational : Set where
  constructor mixed
  field whole : Int
        part : Fraction
open Rational
_≼_ : Rational → Rational → Set
x ≼ y = (whole x Z.≤ whole y) × (whole y Z.≤ whole x → part x ⊆ part y)
reflexive : ∀ x → x ≼ x
reflexive x = Z.rid _ , λ _ m s p → p
transitive : ∀ x y z → x ≼ y → y ≼ z → x ≼ z
transitive x y z (p , f) (q , g) = Z.chain p q , λ h m s a →
  g (Z.chain h p) m s (f (Z.chain q h) m s a)
embed : Int → Rational
embed z = mixed z zero
floor = whole
lower : ∀ z x → embed z ≼ x → z Z.≤ floor x
lower z x = fst
upper : ∀ z x → z Z.≤ floor x → embed z ≼ x
upper z x le = le , λ _ → least (part x)
