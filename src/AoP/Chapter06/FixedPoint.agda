{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.FixedPoint where

open import Agda.Primitive using (Level; _⊔_)

-- §6.2. Only the infimum of the prefixpoints is needed. Keeping that
-- hypothesis explicit works for large carriers without resizing predicates.
module KnasterTarski {c r : Level} {L : Set c}
  (_≤_ : L → L → Set r) (trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
  (Φ : L → L)
  (mono : ∀ {x y} → x ≤ y → Φ x ≤ Φ y) where

  Prefix : L → Set r
  Prefix x = Φ x ≤ x

  record Infimum (μ : L) : Set (c ⊔ r) where
    field
      lower : ∀ x → Prefix x → μ ≤ x
      greatest : ∀ z → (∀ x → Prefix x → z ≤ x) → z ≤ μ

  module Proof {μ} (inf : Infimum μ) where
    open Infimum inf

    fold : Φ μ ≤ μ
    fold = greatest (Φ μ) λ x pre → trans (mono (lower x pre)) pre

    unfold : μ ≤ Φ μ
    unfold = lower (Φ μ) (mono fold)

    least : ∀ x → Φ x ≤ x → μ ≤ x
    least = lower
