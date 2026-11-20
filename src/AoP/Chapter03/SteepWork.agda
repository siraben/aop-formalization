{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.SteepWork where

open import AoP.Common.Prelude
open import AoP.Chapter03.Steep using (sum; scan; step)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _<_)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 3.3. Count additions in suffix sums. In the direct test,
-- short-circuit conjunction skips later tests once a comparison fails.
-- On an input that passes every comparison, no suffix test is skipped.
size : List Nat → Nat
size [] = 0
size (_ ∷ xs) = suc (size xs)
work : List Nat → Nat
work [] = 0
work (a ∷ xs) with sum xs < a
... | true = size xs + work xs
... | false = size xs

-- Generate an input that forces every test: choose each new head one
-- larger than the sum of the tail. This includes the singleton [1].
hard : Nat → List Nat
hard zero = []
hard (suc n) = suc (sum (hard n)) ∷ hard n
length-law : ∀ n → size (hard n) ≡ n
length-law zero = refl
length-law (suc n) = cong suc (length-law n)
less-next : ∀ n → (n < suc n) ≡ true
less-next zero = refl
less-next (suc n) = less-next n
triangle : Nat → Nat
triangle zero = 0
triangle (suc n) = n + triangle n
attained : ∀ n → work (hard n) ≡ triangle n
attained zero = refl
attained (suc n) rewrite less-next (sum (hard n)) | length-law n | attained n = refl

open import AoP.Common.NatOrder using (_≤_; z≤; rid; sum-mono)

upper : ∀ xs → work xs ≤ triangle (size xs)
upper [] = z≤
upper (a ∷ xs) with sum xs < a
... | true = sum-mono (rid (size xs)) (upper xs)
... | false = prefix (size xs) _
  where prefix : ∀ n m → n ≤ n + m
        prefix zero m = z≤
        prefix (suc n) m = AoP.Common.NatOrder.s≤ (prefix n m)

-- Count the cached fold's additions when computing the full pair. A
-- step does one sum update regardless of the Boolean in the pair.
counted : List Nat → (Nat × Bool) × Nat
counted [] = (0 , true) , 0
counted (a ∷ xs) with counted xs
... | state , count = step a state , suc count
cached : ∀ xs → counted xs ≡ (scan xs , size xs)
cached [] = refl
cached (a ∷ xs) rewrite cached xs = refl
