{-# OPTIONS --safe --without-K #-}
module AoP.DigitInterval where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; chain; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Exercise 10.12. Write the scaled decimal fraction as n/w (w > 0).
-- A digit d with d ≤ n/w < d+1 has numerator in the half-open cell
-- [d*w,(d+1)*w). Adjacent cells cannot share even their boundary.
Cell : Nat → Nat → Nat → Set
Cell w n d = ((d * w) ≤ n) × (suc n ≤ (suc d * w))

private
  scale : ∀ w {a b} → a ≤ b → a * w ≤ b * w
  scale w z≤ = z≤
  scale w (s≤ le) = sum-mono (rid w) (scale w le)
  absurd : ∀ {a} {X : Set} → suc a ≤ a → X
  absurd {0} ()
  absurd {suc a} (s≤ p) = absurd p
  discrete : ∀ a b → ((suc a ≤ b) → a ≡ b) → ((suc b ≤ a) → a ≡ b) → a ≡ b
  discrete 0 0 l r = refl
  discrete 0 (suc b) l r = l (s≤ z≤)
  discrete (suc a) 0 l r = r (s≤ z≤)
  discrete (suc a) (suc b) l r = cong suc (discrete a b (λ p → inject (l (s≤ p))) (λ p → inject (r (s≤ p))))
    where inject : ∀ {i j} → suc i ≡ suc j → i ≡ j
          inject refl = refl

unique : ∀ w n a b → Cell w n a → Cell w n b → a ≡ b
unique w n a b (la , ua) (lb , ub) = discrete a b
  (λ p → absurd (chain ua (chain (scale w p) lb)))
  (λ p → absurd (chain ub (chain (scale w p) la)))
