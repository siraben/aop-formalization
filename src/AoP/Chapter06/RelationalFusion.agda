{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.RelationalFusion where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations

-- §5.5, specialized to cons-lists. Push a relation H through a fold.
-- Unlike functional fusion there are two independent inclusions: local
-- simulations suffice for soundness; the opposite simulations give
-- completeness. No assumption that H is single-valued is needed.
module Lists {A B C : Set} (H : C ← B)
             (E : B → Set) (F : B ← (A × B))
             (D : C → Set) (G : C ← (A × C)) where
  module Sound
    (base : ∀ {b c} → H c b → E b → D c)
    (step : ∀ {a b b′ c′} → H c′ b′ → F b′ (a , b) →
            Σ C λ c → G c′ (a , c) × H c b) where

    push : H ∘ Fold E F ⊆ Fold D G
    push (_ , h , nil e) = nil (base h e)
    push (_ , h , cons f tail) with step h f
    ... | c , g , h′ = cons g (push (_ , h′ , tail))

  module Complete
    (base : ∀ {c} → D c → Σ B λ b → H c b × E b)
    (step : ∀ {a b c c′} → G c′ (a , c) → H c b →
            Σ B λ b′ → H c′ b′ × F b′ (a , b)) where

    pull : Fold D G ⊆ H ∘ Fold E F
    pull (nil d) with base d
    ... | b , h , e = b , h , nil e
    pull (cons g tail) with pull tail
    ... | b , h , tail′ with step g h
    ...   | b′ , h′ , f = b′ , h′ , cons f tail′
