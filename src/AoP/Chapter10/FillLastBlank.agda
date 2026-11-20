{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.FillLastBlank where

open import AoP.Common.Prelude
open import AoP.Chapter10.Detab
open import AoP.Chapter10.FilledPrefix using () renaming (module Law to Filled)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter10.Entab using (module Encode)
open import AoP.Chapter10.EntabLength using (module Bound)
open import AoP.Common.NatOrder using (_≤_; rid; chain; weaken; s≤)
open import AoP.Chapter10.FillPrefixes using (Prefix; same; drop; module Restricted)
open import AoP.Chapter01.Snoc using (ε; _▻_)
open import Agda.Builtin.Nat using (Nat; suc)

-- In the proper-prefix case of 10.4, the last character on the
-- longer side must be a blank. Remove the common padding from the
-- right; any remaining letters beyond the shorter prefix are blanks.
module Law {A : Set} (n : Nat) where
  open Expand {A} n
  open Encode {A} n using (snoc-blanks)
  open Restricted {A} n using (V; fill)
  open Bound {A} n using (len; grows)
  private
    back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    back refl = refl
    pred : Text → Text
    pred ε = ε
    pred (xs ▻ _) = xs
    last : Text → Char′ A
    last ε = blank
    last (_ ▻ c) = c
    bound : ∀ {xs ys : Text} → Prefix xs ys → len xs ≤ len ys
    bound same = rid _
    bound (drop b p) = weaken (bound p)
    absurd : ∀ {k} {X : Set} → suc k ≤ k → X
    absurd {0} ()
    absurd {suc k} (s≤ q) = absurd q

  padded : ∀ {xs ys a} → Prefix xs ys → ∀ k l → blanks xs k ≡ blanks (ys ▻ a) l → a ≡ blank
  padded {ys = ys} {a} p 0 l refl = absurd (chain (grows (ys ▻ a) l) (bound p))
  padded {xs} p (suc k) 0 eq = back (cong last (back (snoc-blanks xs k) ∙ eq))
  padded {xs} {ys} {a} p (suc k) (suc l) eq = padded p k l (cong pred (back (snoc-blanks xs k) ∙ eq ∙ snoc-blanks (ys ▻ a) l))

  boundary : ∀ y → (position (y ▻ blank) ≡ n) ⊎ (fill (y ▻ blank) ≡ fill y)
  boundary y with position y
  ... | 0 = inl refl
  ... | suc k = inr refl

  snoc : ∀ {x y a} → V x (y ▻ a) → (x ≡ (y ▻ a)) ⊎ V x y
  snoc (same , eq) = inl refl
  snoc {x} {y} {a} (drop .a p , eq) with padded p (suc (position x)) (suc (position (y ▻ a))) eq
  ... | refl with boundary y
  ...   | inl stop = inl (Filled.at-stop n (y ▻ blank) stop (drop blank p , eq))
  ...   | inr shift = inr (p , (eq ∙ shift))
