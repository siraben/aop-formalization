{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXExternal where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit; digit; intern)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import Agda.Builtin.Nat using (Nat; suc)

-- §10.4 — What should TeX *print*? Reading .5 and .50 gives the same
-- internal value. A printer must round-trip, but that alone would allow
-- any number of redundant zeroes. Its second obligation is minimal length
-- among *all* decimal strings that read back to this particular value.
-- No uniqueness of the minimizing string is assumed.
length : List Digit → Nat
length [] = 0
length (_ ∷ ds) = suc (length ds)

record Shortest (n : Nat) (ds : List Digit) : Set where
  constructor shortest
  field
    round-trip : intern ds ≡ n
    minimal : (es : List Digit) → intern es ≡ n → length ds ≤ length es

-- A tiny checked instance of the specification: .5 represents half a
-- unit (32768 scaled points). The sole shorter candidate is empty and
-- denotes zero. This is an example, not yet the general greedy printer.
five : Digit
five = digit 5 (s≤ (s≤ (s≤ (s≤ (s≤ z≤)))))

half : Shortest 32768 (five ∷ [])
Shortest.round-trip half = refl
Shortest.minimal half [] ()
Shortest.minimal half (_ ∷ _) eq = s≤ z≤

zero-shortest : Shortest 0 []
zero-shortest = shortest refl (λ _ _ → z≤)
