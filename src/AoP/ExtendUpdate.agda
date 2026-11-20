{-# OPTIONS --safe --without-K #-}
module AoP.ExtendUpdate where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (_⊎_; inl; inr)

-- Exercise 3.21. Extend an update on encoded states to every state of
-- the target. On the image, decode, update, and encode. Outside the
-- image, leave the target unchanged. In constructive Agda the case
-- split requires an effective image test returning a preimage on success.
module Extend {A B C : Set} (encode : B → A)
              (injective : ∀ {u v} → encode u ≡ encode v → u ≡ v) where
  Fiber : A → Set
  Fiber a = Σ B (λ b → encode b ≡ a)

  module Decide (image : ∀ a → Fiber a ⊎ (Fiber a → ⊥)) (step : C → B → B) where
    update : C → A → A
    update c a with image a
    ... | inl (b , _) = encode (step c b)
    ... | inr _ = a

    commute : ∀ c b → encode (step c b) ≡ update c (encode b)
    commute c b with image (encode b)
    ... | inl (b′ , eq) = cong (λ x → encode (step c x)) (back (injective eq))
      where back : ∀ {u v : B} → u ≡ v → v ≡ u
            back refl = refl
    ... | inr absent with absent (b , refl)
    ...   | ()
