{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TabPrefixExample where

open import AoP.Common.Prelude
open import AoP.Chapter10.Detab
open import AoP.Chapter01.Snoc using (ε; _▻_)
open import AoP.Chapter10.TabFree using (module Image)
open import AoP.Chapter10.EntabMinimum using (module Optimal)
open import AoP.Chapter10.EntabLength using (module Bound)
open import AoP.Common.NatOrder using (_≤_; chain; s≤)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)

-- §10.2. At width eight, five glyphs and a tab occupy eight columns
-- with six encoded characters. Cut off the last expanded blank: no
-- six-character encoding reaches that seventh column with this text.
open Expand {Nat} 7
open Image {Nat} 7
open Bound {Nat} 7 using (len)
open Optimal {Nat} 7 using (shortest)

five : Text
five = ε ▻ glyph 0 ▻ glyph 1 ▻ glyph 2 ▻ glyph 3 ▻ glyph 4
prefix = five ▻ blank ▻ blank
code = five ▻ tab
expansion : detab code ≡ prefix ▻ blank
expansion = refl

lower : ∀ xs → detab xs ≡ prefix → 7 ≤ len xs
lower xs = shortest (space (space (plain five))) xs

impossible : ∀ xs → detab xs ≡ prefix → len xs ≤ len code → ⊥
impossible xs eq le with chain (lower xs eq) le
... | s≤ (s≤ (s≤ (s≤ (s≤ (s≤ ())))))
