{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DecimalBracketCost where

open import AoP.Common.Prelude
open import AoP.Chapter09.Bracketing using (module Model)
open import AoP.Chapter01.Trees using (tip; bin)
open import AoP.Chapter06.DecimalAccumulator using (printer)
open import AoP.Chapter01.ConversionCost using (len)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Exercises 9.8–9.9. Cache the numerical result as the size summary:
-- equal operand widths can yield different result widths (9+1 vs 1+1).
-- Recover the exact decimal width from the canonical expansion.
width : Nat → Nat
width n = len (printer n)
max : Nat → Nat → Nat
max 0 n = n
max (suc m) 0 = suc m
max (suc m) (suc n) = suc (max m n)

-- Addition counts aligned input columns; emitting a final carry is
-- outside this count. Schoolbook multiplication counts one single-digit
-- product per pair, excluding accumulation and carry propagation.
module Sum = Model (λ n → n) _+_ (λ x y → max (width x) (width y))
module Product = Model (λ n → n) _*_ (λ x y → width x * width y)

-- The 9+1 carry widens the next addition. Multiplying 9 by 2
-- similarly increases the number of elementary products at the root.
sum-left : Sum.cost (bin (bin (tip 9) (tip 1)) (tip 1)) ≡ 3
sum-left = refl
sum-right : Sum.cost (bin (tip 9) (bin (tip 1) (tip 1))) ≡ 2
sum-right = refl
product-left : Product.cost (bin (bin (tip 9) (tip 2)) (tip 1)) ≡ 3
product-left = refl
product-right : Product.cost (bin (tip 9) (bin (tip 2) (tip 1))) ≡ 2
product-right = refl
