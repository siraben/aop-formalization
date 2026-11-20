{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXGreedyTieTrace where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit; digit; intern)
open import AoP.Common.NatOrder using (z≤; s≤)
open import Agda.Builtin.Nat using (Nat; suc; _*_; _-_; div-helper)

-- §10.4, exercise 10.15. Follow the printed upper-endpoint rule
-- for a single target. Saturating a negative lower endpoint to zero
-- implements the stop test p ≤ 0. Running out of fuel is observable.
data Run : Set where
  exhausted done : Run
  emit : Nat → Run → Run
run : Nat → Nat → Nat → Run
run k 0 q = done
run 0 (suc p) q = exhausted
run (suc k) (suc p) q = emit d (run k (10 * suc p - 131072 * d) (10 * q - 131072 * d))
  where d = div-helper 0 131071 (10 * q) 131071

-- Initial endpoints (2n−1,2n+1) = (19,21). Three initial zeroes
-- leave (19000,21000); digit 1 leaves (58928,78928).
first-nonzero : run 2 19000 21000 ≡ emit 1 (run 1 58928 78928)
first-nonzero = refl
printed : run 5 19 21 ≡ emit 0 (emit 0 (emit 0 (emit 1 (emit 6 done))))
printed = refl

candidate : Digit → List Digit
candidate d = z ∷ z ∷ z ∷ digit 1 (s≤ z≤) ∷ d ∷ []
  where z = digit 0 z≤
five six : Digit
five = digit 5 (s≤ (s≤ (s≤ (s≤ (s≤ z≤)))))
six = digit 6 (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ z≤))))))
printed-reads : intern (candidate six) ≡ 10
printed-reads = refl
rival-reads : intern (candidate five) ≡ 10
rival-reads = refl
-- Absolute error numerators on the common denominator 100000·65536.
printed-error : 16 * 65536 - 10 * 100000 ≡ 48576
printed-error = refl
rival-error : 10 * 100000 - 15 * 65536 ≡ 16960
rival-error = refl
