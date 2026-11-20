{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.InitialSegmentImage where

open import AoP.Common.Prelude
open import AoP.Chapter04.Power using (ℙ; ℰ; _≐_)
open import AoP.Common.NatOrder using (_≤_; rid; chain; s≤; z≤)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import Agda.Builtin.Nat using (Nat)

-- §2.2. The existential image under ≤ contains n whenever some input
-- m lies above n. It is the least downward-closed set containing X;
-- the witness proof works for arbitrary predicates, even empty ones.
segment : ℙ Nat → ℙ Nat
segment X = ℰ _≤_ X
contains : ∀ X n → X n → segment X n
contains X n x = n , (rid n , x)
down : ∀ X {n m} → n ≤ m → segment X m → segment X n
down X le (k , (bound , x)) = k , (chain le bound , x)
least : ∀ (X Y : ℙ Nat) → (∀ n → X n → Y n) → (∀ {n m} → n ≤ m → Y m → Y n) → ∀ n → segment X n → Y n
least X Y include closed n (m , (le , x)) = closed le (include m x)

-- For {1,4}, the larger input supplies every witness through 4. Any
-- alleged image member must be bounded by either 1 or 4, hence by 4.
seed : ℙ Nat
seed n = n ∈ (1 ∷ 4 ∷ [])
trace : segment seed ≐ (λ n → n ≤ 4)
trace = (λ n w → least seed (_≤ 4) upper chain n w) , (λ n p → 4 , (p , there here))
  where upper : ∀ n → seed n → n ≤ 4
        upper _ here = s≤ z≤
        upper _ (there here) = rid 4
