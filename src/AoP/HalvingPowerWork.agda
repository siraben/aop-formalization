{-# OPTIONS --safe --without-K #-}
module AoP.HalvingPowerWork where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import AoP.HalvingRun using (half; module Run)
open import AoP.HalvingDigits using (double)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (false; true)

-- §6.4. Count multiplications, assuming the recursive result is shared:
-- one square for each processed bit and one additional multiplication
-- by the base when the bit is set. No cost for finding the bit or for
-- the size of the operands is included in this operation count.
module Cost = Run 0 (λ { false n → suc n ; true n → suc (suc n) })
pow2 : Nat → Nat
pow2 0 = 1
pow2 (suc k) = double (pow2 k)

-- If n fits below twice a limit then its quotient fits below the
-- limit. Strip two from n and one from the limit at every step.
shrink : ∀ n q → suc n ≤ double q → suc (half n) ≤ q
shrink n 0 ()
shrink 0 (suc q) p = s≤ z≤
shrink 1 (suc q) p = s≤ z≤
shrink (suc (suc n)) (suc q) (s≤ (s≤ p)) = s≤ (shrink n q p)

bound : ∀ k n → suc n ≤ pow2 k → Cost.solve n ≤ double k
bound k 0 p = z≤
bound 0 (suc n) (s≤ ())
bound (suc k) (suc n) p rewrite Cost.recurrence n with AoP.HalvingRun.low (suc n) | bound k (half (suc n)) (shrink (suc n) (pow2 k) p)
... | false | h = s≤ (AoP.NatOrder.weaken h)
... | true | h = s≤ (s≤ h)

-- The bound is attained when every bit is one. Appending another
-- one doubles the exponent and adds one, hence triggers both charges.
ones : Nat → Nat
ones 0 = 0
ones (suc k) = suc (double (ones k))
private
  odd-half : ∀ n → half (suc (double n)) ≡ n
  odd-half 0 = refl
  odd-half (suc n) = cong suc (odd-half n)
  odd-bit : ∀ n → AoP.HalvingRun.low (suc (double n)) ≡ true
  odd-bit 0 = refl
  odd-bit (suc n) = odd-bit n
size : ∀ k → suc (ones k) ≡ pow2 k
size 0 = refl
size (suc k) = cong double (size k)
tight : ∀ k → Cost.solve (ones k) ≡ double k
tight 0 = refl
tight (suc k) rewrite Cost.recurrence (double (ones k)) | odd-bit (ones k) | odd-half (ones k) | tight k = refl

-- 13 = 1101₂: four squares and three multiplications by the base.
example : Cost.solve 13 ≡ 7
example = refl
