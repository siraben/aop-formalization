{-# OPTIONS --safe --without-K #-}
module AoP.TeXGridStop where

open import AoP.Prelude
open import AoP.OpenUpperDigit using (Upper)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; chain; sum-mono)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- §10.4. At one decimal width, let [L,H) be the integer-scaled
-- interval. Once z is the greatest grid point below H, a single
-- comparison to L decides feasibility of the entire width.
InCell : Nat → Nat → Nat → Nat → Set
InCell w L H t = (L ≤ t * w) × (suc (t * w) ≤ H)
private
  scale : ∀ w {x y} → x ≤ y → x * w ≤ y * w
  scale w z≤ = z≤
  scale w (s≤ p) = sum-mono (rid w) (scale w p)
  clash : ∀ {n} {X : Set} → suc n ≤ n → X
  clash {0} ()
  clash {suc n} (s≤ p) = clash p
  split : ∀ a b {X : Set} → (a ≤ b → X) → (suc b ≤ a → X) → X
  split 0 b f g = f z≤
  split (suc a) 0 f g = g (s≤ z≤)
  split (suc a) (suc b) f g = split a b (λ p → f (s≤ p)) (λ p → g (s≤ p))

module Grid (w L H z : Nat) (upper : Upper w H z) where
  dominates : ∀ t → suc (t * w) ≤ H → t ≤ z
  dominates t admissible = split t z (λ p → p) (λ later → clash (chain admissible (chain (snd upper) (scale w later))))
  stop : L ≤ z * w → InCell w L H z
  stop ok = ok , fst upper
  skip : suc (z * w) ≤ L → ∀ t → InCell w L H t → ⊥
  skip gap t (lo , hi) = clash (chain gap (chain lo (scale w (dominates t hi))))
