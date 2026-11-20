{-# OPTIONS --safe --without-K #-}
module AoP.UniqueFixedBounds where

open import AoP.FixedPoint using (module KnasterTarski)

-- §6.2. A unique fixed point serves both for induction and for
-- coinduction. Apply the same infimum proof to the reversed order:
-- its prefixpoints are exactly the original postfixed points.
module Order {c r} {L : Set c} (_≤_ : L → L → Set r)
  (trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
  (Φ : L → L) (mono : ∀ {x y} → x ≤ y → Φ x ≤ Φ y) where
  module Down = KnasterTarski _≤_ trans Φ mono
  module Up = KnasterTarski (λ x y → y ≤ x) (λ xy yz → trans yz xy) Φ mono
  module Unique {μ ν fold : L} (inf : Down.Infimum μ) (sup : Up.Infimum ν)
    (at-most : ∀ x → Φ x ≤ x → x ≤ Φ x → x ≤ fold)
    (at-least : ∀ x → Φ x ≤ x → x ≤ Φ x → fold ≤ x) where
    -- The infimum is fixed, so fold lies below it. Every prefixed
    -- candidate lies above that infimum: this gives equation (6.2).
    induction : ∀ x → Φ x ≤ x → fold ≤ x
    induction x pre = trans (at-least μ (Down.Proof.fold inf) (Down.Proof.unfold inf)) (Down.Proof.least inf x pre)
    -- Dually the supremum is fixed. Every postfixed candidate lies
    -- below it, and uniqueness puts it below fold: equation (6.3).
    coinduction : ∀ x → x ≤ Φ x → x ≤ fold
    coinduction x post = trans (Up.Proof.least sup x post) (at-most ν (Up.Proof.unfold sup) (Up.Proof.fold sup))
