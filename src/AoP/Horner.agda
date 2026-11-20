{-# OPTIONS --safe --without-K #-}
module AoP.Horner where

open import AoP.Prelude
open import AoP.Folds

map : ∀ {A B : Set} → (A → B) → List A → List B
map f = ⦅ [] ∣ (λ x ys → f x ∷ ys) ⦆

-- Applying f to every successive tail applies it i times at index i.
tri : ∀ {A : Set} → (A → A) → List A → List A
tri f = ⦅ [] ∣ (λ x ys → x ∷ map f ys) ⦆

module Ruby {A : Set} (e : A) (_⊛_ : A → A → A) (f : A → A)
            (base : e ≡ f e) (step : ∀ x y → f x ⊛ f y ≡ f (x ⊛ y)) where
  reduce : List A → A
  reduce = ⦅ e ∣ _⊛_ ⦆

  -- The algebra endomorphism can be moved outside the reduction.
  promote : ∀ xs → reduce (map f xs) ≡ f (reduce xs)
  promote [] = base
  promote (x ∷ xs) = cong (f x ⊛_) (promote xs) ∙ step x (reduce xs)

  -- Replace the materialised triangle with one traversal (§3.2).
  horner : ∀ xs → reduce (tri f xs) ≡ ⦅ e ∣ (λ x y → x ⊛ f y) ⦆ xs
  horner = fusion reduce [] (λ x ys → x ∷ map f ys) (λ x y → x ⊛ f y)
                  (λ x ys → cong (x ⊛_) (promote ys))
