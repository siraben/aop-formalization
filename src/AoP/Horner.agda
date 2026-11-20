{-# OPTIONS --safe --without-K #-}
module AoP.Horner where

-- §3.2 — How can a polynomial be evaluated without computing powers?
-- Read [a,b,c] as coefficients in ascending order. At x, the triangle
-- transforms this list into [a,b*x,c*x*x], which we then sum. Horner's
-- rule computes the same value as a + (b + c*x)*x, without building the
-- transformed list. For [2,3,4] at 10, both routes give 432.
--
-- `Ruby` abstracts this example: e is zero, _⊛_ is addition, and f
-- multiplies by x. `base` and `step` express exactly what the calculation
-- uses: multiplying zero gives zero and multiplication distributes over
-- addition. Read `horner` as the theorem and `promote` as its key step.

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
  promote (x ∷ xs) = begin
    reduce (map f (x ∷ xs))
      ≡⟨⟩  -- map and reduce on cons
    f x ⊛ reduce (map f xs)
      ≡⟨ cong (f x ⊛_) (promote xs) ⟩  -- induction hypothesis
    f x ⊛ f (reduce xs)
      ≡⟨ step x (reduce xs) ⟩  -- f preserves the algebra
    f (reduce (x ∷ xs)) ∎

  -- Replace the materialised triangle with one traversal (§3.2).
  horner : ∀ xs → reduce (tri f xs) ≡ ⦅ e ∣ (λ x y → x ⊛ f y) ⦆ xs
  horner = fusion reduce [] (λ x ys → x ∷ map f ys) (λ x y → x ⊛ f y)
                  (λ x ys → cong (x ⊛_) (promote ys))
