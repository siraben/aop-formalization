{-# OPTIONS --safe --without-K #-}
module AoP.TeXDistanceExample where

open import AoP.Prelude
open import AoP.TeXFraction using (intern)
open import AoP.RoundingCollision using (suffix; seven; eight)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)

-- Exercise 10.15. Equal width and identical round trips can still give
-- different distances. Cross-multiply by the common positive denominator
-- 100000 * 65536 to compare the errors without rational division.
left-read : intern (suffix seven) ≡ 5
left-read = refl
right-read : intern (suffix eight) ≡ 5
right-read = refl
left-distance : 7 * 65536 + 41248 ≡ 5 * 100000
left-distance = refl
right-distance : 5 * 100000 + 24288 ≡ 8 * 65536
right-distance = refl
-- The error of .00007 exceeds that of .00008 by 16960 in these units.
excess : 24288 + 16960 ≡ 41248
excess = refl
