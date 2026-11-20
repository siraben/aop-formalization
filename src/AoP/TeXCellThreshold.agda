{-# OPTIONS --safe --without-K #-}
module AoP.TeXCellThreshold where

open import AoP.Prelude
open import AoP.GridTranslation using (Below)
open import AoP.NatOrder using (_≤_; z≤; s≤; chain; sum-mono; rid)
open import AoP.DigitInterval using (Cell)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Compare integer thresholds before and after taking the floor. This
-- transports a half-open rounding cell to the original numerator.
private
  scale : ∀ v {a b} → a ≤ b → a * v ≤ b * v
  scale v z≤ = z≤
  scale v (s≤ p) = sum-mono (rid v) (scale v p)
  split : ∀ a b {X : Set} → (a ≤ b → X) → (suc b ≤ a → X) → X
  split 0 b f g = f z≤
  split (suc a) 0 f g = g (s≤ z≤)
  split (suc a) (suc b) f g = split a b (λ p → f (s≤ p)) (λ p → g (s≤ p))
  clash : ∀ {n} {X : Set} → suc n ≤ n → X
  clash {0} ()
  clash {suc n} (s≤ p) = clash p

module At (v N s : Nat) (floor : Cell v N s) where
  lower : ∀ a → a ≤ s → a * v ≤ N
  lower a p = chain (scale v p) (fst floor)
  upper : ∀ b → suc s ≤ b → suc N ≤ b * v
  upper b p = chain (snd floor) (scale v p)
  lower-back : ∀ a → a * v ≤ N → a ≤ s
  lower-back a p = split a s (λ h → h) (λ h → clash (chain (upper a h) p))
  upper-back : ∀ b → suc N ≤ b * v → suc s ≤ b
  upper-back b p = split b s (λ h → clash (chain p (lower b h))) (λ h → h)
