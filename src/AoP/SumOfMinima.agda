{-# OPTIONS --safe --without-K #-}
module AoP.SumOfMinima where

open import AoP.Prelude
open import AoP.Thinning using (Min)
open import AoP.NatOrder using (_≤_; sum-mono)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §7.2, addition as a monotonic algebra. Choose a number from each
-- of two sets and add them. If the individual minima are m and n,
-- then m+n is attainable and bounds every attainable sum below.
module Law (X Y : Nat → Set) where
  Sums : Nat → Set
  Sums s = Σ Nat λ x → Σ Nat λ y → X x × (Y y × (x + y ≡ s))

  distribute : ∀ m n → Min _≤_ m X → Min _≤_ n Y → Min _≤_ (m + n) Sums
  distribute m n (xm , leastX) (yn , leastY) = (m , n , xm , yn , refl) , bound
    where bound : ∀ s → Sums s → m + n ≤ s
          bound _ (x , y , xx , yy , refl) = sum-mono (leastX x xx) (leastY y yy)
