{-# OPTIONS --safe --without-K #-}
module AoP.UniformCodeCost where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.ConversionCost using (len)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Exercise 9.19. Each code element occupies the same number of bits.
-- A shortest feasible list of code elements therefore minimizes bits,
-- even if the common charge is zero (in which case all costs tie).
module Law {A : Set} where
  open Text {A}
  bits : Nat → Nat → List Code → Nat
  bits c p [] = 0
  bits c p (sym a ∷ xs) = c + bits c p xs
  bits c p (ptr i k ∷ xs) = p + bits c p xs

  uniform : ∀ w xs → bits w w xs ≡ len xs * w
  uniform w [] = refl
  uniform w (sym a ∷ xs) = cong (w +_) (uniform w xs)
  uniform w (ptr i k ∷ xs) = cong (w +_) (uniform w xs)

  private
    scale : ∀ {n m} w → n ≤ m → n * w ≤ m * w
    scale w z≤ = z≤
    scale w (s≤ p) = sum-mono (rid w) (scale w p)

  preserve : ∀ w xs ys → len xs ≤ len ys → bits w w xs ≤ bits w w ys
  preserve w xs ys p rewrite uniform w xs | uniform w ys = scale w p
