{-# OPTIONS --safe --without-K #-}
module AoP.OpenUpperDigit where

open import AoP.Prelude
open import AoP.DigitInterval using (Cell; unique)
open import AoP.NatOrder using (_≤_; s≤)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Exercise 10.14. When the upper endpoint is excluded, choose the
-- greatest digit strictly below 10q/w. For N = 10q > 0 this means
-- d*w < N ≤ (d+1)*w. Ordinary floor division on N-1 handles exact
-- multiples too, without a divisibility test. Assume positive w.
Upper : Nat → Nat → Nat → Set
Upper w N d = (suc (d * w) ≤ N) × (N ≤ suc d * w)

correct : ∀ w m d → Cell w m d → Upper w (suc m) d
correct w m d (lo , hi) = s≤ lo , hi

recover : ∀ w m d → Upper w (suc m) d → Cell w m d
recover w m d (s≤ lo , hi) = lo , hi

only : ∀ w m a b → Upper w (suc m) a → Upper w (suc m) b → a ≡ b
only w m a b x y = unique w m a b (recover w m a x) (recover w m b y)

-- The unrestricted nonintegrality claim fails even for the TeX scale:
-- q = w/2 gives the exact upper endpoint 5. The strict choice is 4.
endpoint : 10 * 65536 ≡ 5 * 131072
endpoint = refl
