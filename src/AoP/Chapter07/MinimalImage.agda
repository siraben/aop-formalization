{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MinimalImage where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter07.MinimalComparison using (Test)
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.22. Compute minimal elements after mapping a set through
-- f, or compare in the source via f and then map its minimal elements.
-- Membership in the image supplies the preimage needed in each proof;
-- f need not be injective and no choice of a global inverse is used.
module Law {A B : Set} (f : A → B) (R : B ← B) (X : A → Set) where
  image : (A → Set) → B → Set
  image P b = Σ A λ a → P a × (f a ≡ b)

  pull : A ← A
  pull a c = R (f a) (f c)

  lift : ∀ {b} → Min (Test R) b (image X) → image (λ a → Min (Test pull) a X) b
  lift ((a , xa , refl) , minimal) = a , (xa , (λ c xc → minimal (f c) (c , xc , refl))) , refl

  lower : ∀ {b} → image (λ a → Min (Test pull) a X) b → Min (Test R) b (image X)
  lower (a , (xa , minimal) , refl) = (a , xa , refl) , λ { _ (c , xc , refl) → minimal c xc }
