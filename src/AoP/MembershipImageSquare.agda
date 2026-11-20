{-# OPTIONS --safe --without-K #-}
module AoP.MembershipImageSquare where

open import AoP.Prelude
open import AoP.Power using (ℙ; ℰ; _≐_)
open import AoP.Relations using (_←_)

-- §2.3: R after membership equals membership after the graph of ℰ R.
-- A graph edge identifies its output set extensionally. Keeping that
-- set explicit shows exactly which witness the two paths exchange.
module Square {A B : Set} (R : B ← A) (X : ℙ A) where
  choose-first : B → Set
  choose-first b = Σ A (λ a → R b a × X a)
  image-first : B → Set₁
  image-first b = Σ (ℙ B) (λ Y → (ℰ R X ≐ Y) × Y b)

  across : ∀ b → choose-first b → image-first b
  across b (a , (r , x)) = ℰ R X , (((λ _ p → p) , (λ _ p → p)) , (a , (r , x)))
  back : ∀ b → image-first b → choose-first b
  back b (Y , ((into , from) , y)) = from b y
