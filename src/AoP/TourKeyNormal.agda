{-# OPTIONS --safe --without-K #-}
module AoP.TourKeyNormal where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import AoP.TourThinProjection using (module Law)

-- Exercise 8.25. Equality of two *adjacent* keys is precisely the
-- obstruction to regarding a compacted candidate list as unchanged.
-- Nonadjacent repetitions do not affect this calculation.
module Normal {K : Set} (eq : ∀ (x y : K) → (x ≡ y) ⊎ (x ≡ y → ⊥)) where
  open Law {Tour = K} (λ k → k) (λ _ → 0) eq using (compact; push)
  data Apart : List K → Set where
    empty : Apart []
    single : ∀ x → Apart (x ∷ [])
    cons : ∀ {x y xs} → (x ≡ y → ⊥) → Apart (y ∷ xs) → Apart (x ∷ y ∷ xs)
  fixed : ∀ {xs} → Apart xs → compact xs ≡ xs
  fixed empty = refl
  fixed (single x) = refl
  fixed (cons {x} {y} {xs} dis rest) rewrite fixed rest with eq x y
  ... | inr _ = refl
  ... | inl e with dis e
  ...   | ()

  pushed : ∀ x {ys} → Apart ys → Apart (push x ys)
  pushed x empty = single x
  pushed x {y ∷ ys} norm with eq x y
  ... | inl _ = norm
  ... | inr ne = cons ne norm
  output : ∀ xs → Apart (compact xs)
  output [] = empty
  output (x ∷ xs) = pushed x (output xs)
