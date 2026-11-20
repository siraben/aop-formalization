{-# OPTIONS --safe --without-K #-}
module AoP.FibreTieTrace where

open import AoP.Prelude
open import AoP.FibrePowerThinning using (module Law)
open import AoP.PowerRelator using (Lift; cover)
open import AoP.NatOrder using (_≤_; rid; s≤; z≤; chain)
open import AoP.Thinning using (Min)
open import Agda.Builtin.Nat using (Nat)

-- Two enabled intermediate states, three routes. The first state has
-- tied minima; selecting just one is enough for the global objective.
data Station : Set where west east : Station
data Route : Set where red blue green : Route
data Finish : Route → Station → Set where
  r : Finish red west
  b : Finish blue west
  g : Finish green east
cost : Route → Nat
cost red = 2
cost blue = 2
cost green = 5
Order = λ x y → cost x ≤ cost y
open Law Finish Order Order fst
data Kept : Route → Set where blue′ : Kept blue; green′ : Kept green
choices : Lift M Kept (λ _ → ⊤)
choices = cover back forth
  where
  west-min : M blue west
  west-min = b , λ { _ r → rid 2 ; _ b → rid 2 }
  east-min : M green east
  east-min = g , λ { _ g → rid 5 }
  back : ∀ x → Kept x → Σ Station λ i → ⊤ × M x i
  back .blue blue′ = west , tt , west-min
  back .green green′ = east , tt , east-min
  forth : ∀ i → ⊤ → Σ Route λ x → Kept x × M x i
  forth west _ = blue , blue′ , west-min
  forth east _ = green , green′ , east-min
best : Min Order blue (Reach (λ _ → ⊤))
best = minimum (λ le → le) chain choices (blue′ , λ { _ blue′ → rid 2 ; _ green′ → s≤ (s≤ z≤) })
