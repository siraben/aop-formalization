{-# OPTIONS --safe --without-K #-}
module AoP.TeXClosestTrace where

open import AoP.Prelude
open import AoP.TeXNumeratorBounds using (module Range)
open import AoP.TeXNearestNeighbours using (err)
open import AoP.StrictUpperQuotient using (choose)

-- Exercise 10.15: refine the greedy five-place output .00016 for
-- target 10. The admissible p satisfy 1900000 ≤ 131072p < 2100000.
-- At width five the target numerator is 10·100000 on the error scale.
module R = Range 131071 1900000 2099999 99999
first-feasible : R.ceil 1900000 ≡ 15
first-feasible = refl
last-feasible : R.hi ≡ 16
last-feasible = refl
below-target : choose 65535 1000000 ≡ 15
below-target = refl
lower-error : err 983040 1000000 ≡ 16960
lower-error = refl
upper-error : err 1048576 1000000 ≡ 48576
upper-error = refl
