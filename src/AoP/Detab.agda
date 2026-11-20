{-# OPTIONS --safe --without-K #-}
module AoP.Detab where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_; foldl)

-- §10.2. The state counts extra blanks before the next tab stop: if it
-- is zero, a tab still consumes one column. A width of suc n is positive
-- by construction. Line breaks reset the state; glyphs consume one column.
data Char′ (A : Set) : Set where
  glyph : A → Char′ A
  blank tab newline : Char′ A

module Expand {A : Set} (n : Nat) where
  Text = Snoc (Char′ A)

  advance : Nat → Nat
  advance zero = n
  advance (suc k) = k

  position : Text → Nat
  position = foldl n λ where
    k newline → n
    k _ → advance k

  blanks : Text → Nat → Text
  blanks xs zero = xs
  blanks xs (suc k) = blanks (xs ▻ blank) k

  -- Consume exactly the remaining columns. The strengthened induction
  -- hypothesis applies to any prefix in the stated position.
  reset : ∀ k xs → position xs ≡ k → position (blanks xs (suc k)) ≡ n
  reset zero xs pos rewrite pos = refl
  reset (suc k) xs pos = reset k (xs ▻ blank) (cong advance pos)

  expand : Text → Char′ A → Text
  expand xs tab = blanks xs (suc (position xs))
  expand xs c = xs ▻ c

  detab : Text → Text
  detab = foldl ε expand

  -- Fuse the position scan into the main fold. The second projection is
  -- the position of the *expanded* prefix, not of the original input.
  step : Text × Nat → Char′ A → Text × Nat
  step (xs , k) tab = blanks xs (suc k) , n
  step (xs , k) newline = xs ▻ newline , n
  step (xs , k) blank = xs ▻ blank , advance k
  step (xs , k) (glyph a) = xs ▻ glyph a , advance k

  state : Text → Text × Nat
  state = foldl (ε , n) step

  pack : Text → Text × Nat
  pack xs = xs , position xs

  square : ∀ xs c → step (pack xs) c ≡ pack (expand xs c)
  square xs tab rewrite reset (position xs) xs refl = refl
  square xs newline = refl
  square xs blank = refl
  square xs (glyph a) = refl

  invariant : ∀ xs → state xs ≡ pack (detab xs)
  invariant ε = refl
  invariant (xs ▻ c) = begin
    step (state xs) c         ≡⟨ cong (λ s → step s c) (invariant xs) ⟩
    step (pack (detab xs)) c  ≡⟨ square (detab xs) c ⟩
    pack (detab (xs ▻ c)) ∎
