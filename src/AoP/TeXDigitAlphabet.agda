{-# OPTIONS --safe --without-K #-}
module AoP.TeXDigitAlphabet where

open import AoP.Prelude
open import AoP.TeXFraction using (Digit; digit)
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import AoP.Subsequences using (_∈_; here; there; image)
open import AoP.Horner using (map)
open import Agda.Builtin.Nat using (Nat; suc)

-- §10.4. A finite reference search needs every legal decimal digit,
-- including every possible witness of its range bound. Generate the
-- alphabet by raising a smaller alphabet and adjoining zero.
Bounded : Nat → Set
Bounded n = Σ Nat λ i → i ≤ n
raise : ∀ {n} → Bounded n → Bounded (suc n)
raise (i , le) = suc i , s≤ le
alphabet : ∀ n → List (Bounded n)
alphabet 0 = (0 , z≤) ∷ []
alphabet (suc n) = (0 , z≤) ∷ map raise (alphabet n)
all-in : ∀ n (x : Bounded n) → x ∈ alphabet n
all-in 0 (0 , z≤) = here
all-in (suc n) (0 , z≤) = here
all-in (suc n) (suc i , s≤ le) = there (image raise (all-in n (i , le)))
toDigit : Bounded 9 → Digit
toDigit (i , le) = digit i le
digits = map toDigit (alphabet 9)
complete : ∀ d → d ∈ digits
complete (digit i le) = image toDigit (all-in 9 (i , le))
