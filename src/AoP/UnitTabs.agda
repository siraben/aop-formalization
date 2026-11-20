{-# OPTIONS --safe --without-K #-}
module AoP.UnitTabs where

open import Agda.Builtin.Nat using (Nat; suc)
open import AoP.Prelude
open import AoP.Detab
open import AoP.Entab
open import AoP.TabFree
open import AoP.EntabLength
open import AoP.NatOrder using (_≤_)
open import AoP.Snoc using (ε; _▻_)

-- §10.2, the boundary case of a stop in every column. Here a tab and a
-- blank always occupy exactly one column. Consequently a different choice
-- between them can change the spelling but cannot shorten the encoding.
-- This gives a full optimality check at width one; the general width
-- proof also has to account for tabs standing for several blanks.
module WidthOne {A : Set} where
  open Expand {A} 0
  open Encode {A} 0
  open Image {A} 0
  open Bound {A} 0

  at-stop : ∀ s → position s ≡ 0
  at-stop ε = refl
  at-stop (s ▻ blank) rewrite at-stop s = refl
  at-stop (s ▻ tab) rewrite at-stop s = refl
  at-stop (s ▻ glyph a) rewrite at-stop s = refl
  at-stop (s ▻ newline) = refl

  length-preserved : ∀ xs → len (detab xs) ≡ len xs
  length-preserved ε = refl
  length-preserved (xs ▻ tab) rewrite at-stop (detab xs) = cong suc (length-preserved xs)
  length-preserved (xs ▻ blank) = cong suc (length-preserved xs)
  length-preserved (xs ▻ glyph a) = cong suc (length-preserved xs)
  length-preserved (xs ▻ newline) = cong suc (length-preserved xs)

  shortest : ∀ {s} (p : Plain s) competitor → detab competitor ≡ s →
             len (fst (entab p)) ≤ len competitor
  shortest p competitor refl = transport (length-preserved competitor) (no-longer p)
    where
    transport : ∀ {x y z : Nat} → y ≡ z → x ≤ y → x ≤ z
    transport refl le = le
