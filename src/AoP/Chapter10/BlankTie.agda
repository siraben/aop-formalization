{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.BlankTie where

open import AoP.Common.Prelude
open import AoP.Chapter10.Detab
open import AoP.Chapter01.Snoc using (ε; _▻_)
open import AoP.Chapter10.Entab using (module Encode)
open import AoP.Chapter10.TabFree using (module Image)
open import AoP.Chapter10.EntabLength using (module Bound)
open import AoP.Chapter10.EntabMinimum using (module Optimal)
open import AoP.Common.NatOrder using (_≤_; s≤)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 10.3. A tab that advances just one column ties with a blank
-- in length. Replace precisely these tabs, leaving longer jumps alone.
module Law {A : Set} (n : Nat) where
  open Expand {A} n
  open Bound {A} n using (len)
  open Encode {A} n using (entab)
  open Image {A} n using (Plain)
  open Optimal {A} n using (shortest)

  monotone : ∀ xs ys (c d : Char′ A) → len xs ≤ len ys → len (xs ▻ c) ≤ len (ys ▻ d)
  monotone xs ys c d = s≤

  choose : Nat → Char′ A → Char′ A
  choose _ blank = blank
  choose _ newline = newline
  choose _ (glyph a) = glyph a
  choose 0 tab = blank
  choose (suc _) tab = tab

  prefer : Text → Text
  prefer ε = ε
  prefer (xs ▻ c) = prefer xs ▻ choose (position (detab xs)) c

  same-step : ∀ xs c → expand xs (choose (position xs) c) ≡ expand xs c
  same-step xs blank = refl
  same-step xs newline = refl
  same-step xs (glyph a) = refl
  same-step xs tab with position xs in eq
  ... | 0 = refl
  ... | suc k rewrite eq = refl

  sound : ∀ xs → detab (prefer xs) ≡ detab xs
  sound ε = refl
  sound (xs ▻ c) rewrite sound xs = same-step (detab xs) c
  length-law : ∀ xs → len (prefer xs) ≡ len xs
  length-law ε = refl
  length-law (xs ▻ c) = cong suc (length-law xs)

  encode′ : ∀ {s} → Plain s → Text
  encode′ p = prefer (fst (entab p))
  minimum : ∀ {s} (p : Plain s) xs → detab xs ≡ s → len (encode′ p) ≤ len xs
  minimum p xs eq rewrite length-law (fst (entab p)) = shortest p xs eq
