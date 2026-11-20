{-# OPTIONS --safe --without-K #-}
module AoP.TabCountObjective where

open import AoP.Prelude
open import AoP.Detab
open import AoP.EntabLength using (module Bound)
open import AoP.Snoc using (ε; _▻_)
open import AoP.NatOrder using (_≤_; z≤; s≤; chain; rid)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 10.2. At width two, both TAB and BLANK TAB expand to
-- two blanks. No encoding of those blanks contains more than one tab.
module Example {A : Set} where
  open Expand {A} 1
  open Bound {A} 1 using (len; grows)
  target short long : Text
  target = ε ▻ blank ▻ blank
  short = ε ▻ tab
  long = ε ▻ blank ▻ tab
  short-ok : detab short ≡ target
  short-ok = refl
  long-ok : detab long ≡ target
  long-ok = refl

  tabs : Text → Nat
  tabs ε = 0
  tabs (xs ▻ tab) = suc (tabs xs)
  tabs (xs ▻ _) = tabs xs

  bound : ∀ xs → len xs ≤ len (detab xs)
  bound ε = z≤
  bound (xs ▻ blank) = s≤ (bound xs)
  bound (xs ▻ newline) = s≤ (bound xs)
  bound (xs ▻ glyph a) = s≤ (bound xs)
  bound (xs ▻ tab) = chain (s≤ (bound xs)) (grows (detab xs ▻ blank) (position (detab xs)))

  one : ∀ x → tabs (ε ▻ x) ≤ 1
  one tab = rid 1
  one blank = z≤
  one newline = z≤
  one (glyph _) = z≤

  small : ∀ xs → len xs ≤ 2 → detab xs ≡ target → tabs xs ≤ 1
  small ε _ _ = z≤
  small (ε ▻ tab) _ _ = rid 1
  small (ε ▻ blank) _ _ = z≤
  small (ε ▻ newline) _ _ = z≤
  small (ε ▻ glyph a) _ _ = z≤
  small (ε ▻ tab ▻ tab) _ ()
  small (ε ▻ tab ▻ blank) _ _ = rid 1
  small (ε ▻ tab ▻ newline) _ _ = rid 1
  small (ε ▻ tab ▻ glyph a) _ _ = rid 1
  small (ε ▻ blank ▻ tab) _ _ = rid 1
  small (ε ▻ newline ▻ tab) _ _ = rid 1
  small (ε ▻ glyph a ▻ tab) _ _ = rid 1
  small (ε ▻ x ▻ blank) _ _ = one x
  small (ε ▻ x ▻ newline) _ _ = one x
  small (ε ▻ x ▻ glyph a) _ _ = one x
  small (xs ▻ x ▻ y ▻ z) (s≤ (s≤ ())) _

  maximal : ∀ xs → detab xs ≡ target → tabs xs ≤ tabs long
  maximal xs eq = small xs limit eq
    where limit : len xs ≤ 2
          limit with bound xs
          ... | le rewrite eq = le

  shorter : suc (len short) ≤ len long
  shorter = rid 2
