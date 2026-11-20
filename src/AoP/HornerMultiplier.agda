{-# OPTIONS --safe --without-K #-}
module AoP.HornerMultiplier where

open import AoP.Prelude

-- Exercise 3.12. For polynomial evaluation the triangle scales a
-- coefficient by the evaluation point. Could the fused fold use a
-- different update h on the reduced suffix? Its compatibility equations
-- say h preserves zero and h(a + s) = scale(a) + h(s). Put s = 0:
-- even the constant polynomial with coefficient a forces h(a).
module Unique {A : Set} (zero : A) (_+_ : A → A → A)
              (unit : ∀ a → a + zero ≡ a) (scale : A → A) where
  private
    back : ∀ {a b : A} → a ≡ b → b ≡ a
    back refl = refl

  forced : (h : A → A) → h zero ≡ zero → (∀ a s → h (a + s) ≡ scale a + h s) →
           ∀ a → h a ≡ scale a
  forced h base step a = begin
    h a                ≡⟨ cong h (back (unit a)) ⟩
    h (a + zero)       ≡⟨ step a zero ⟩
    scale a + h zero   ≡⟨ cong (scale a +_) base ⟩
    scale a + zero     ≡⟨ unit (scale a) ⟩
    scale a ∎

  -- Multiplication by a fixed point satisfies these premises precisely
  -- by annihilation of zero and distributivity over addition.
  unique-choice : scale zero ≡ zero → (∀ a b → scale (a + b) ≡ scale a + scale b) →
                  Σ (A → A) λ h → (h zero ≡ zero) × ((∀ a b → h (a + b) ≡ scale a + h b) ×
                    ((k : A → A) → k zero ≡ zero → (∀ a b → k (a + b) ≡ scale a + k b) → ∀ a → k a ≡ h a))
  unique-choice base dist = scale , base , dist , forced
