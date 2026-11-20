{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ContainerMinimumDistribution where

open import AoP.Common.Prelude
open import AoP.Chapter04.Power using (ℙ)
open import AoP.Chapter08.Thinning using (Min)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)

-- §7.2, Theorem 7.1. Fix a constructor shape; its positions index
-- the inputs that may be minimized independently. The proof also
-- covers an empty or infinite position type. A witness of an output
-- carries its whole vector of feasible inputs.
module Law {I A B : Set} (R : A → A → Set) (S : B → B → Set)
  (self : ∀ a → R a a) (alg : (I → A) → B) where
  Image : (I → ℙ A) → ℙ B
  Image pool b = Σ (I → A) λ xs → (∀ i → pool i (xs i)) × (alg xs ≡ b)
  Monotone = ∀ (xs ys : I → A) → (∀ i → R (xs i) (ys i)) → S (alg xs) (alg ys)
  Distributes = ∀ pool xs → (∀ i → Min R (xs i) (pool i)) → Min S (alg xs) (Image pool)

  distribute : Monotone → Distributes
  distribute mono pool xs local = (xs , (λ i → fst (local i)) , refl) ,
    (λ { _ (ys , feasible , refl) → mono xs ys (λ i → snd (local i) _ (feasible i)) })

  -- Conversely, test each coordinate on just its two given values.
  -- The left vector is locally minimal and the right vector is one
  -- feasible competitor. Test distribution against that competitor.
  monotone : Distributes → Monotone
  monotone dist xs ys le = snd (dist pool xs mins) _ (ys , (λ i → inr refl) , refl)
    where
      pool : I → ℙ A
      pool i a = (a ≡ xs i) ⊎ (a ≡ ys i)
      mins : ∀ i → Min R (xs i) (pool i)
      mins i = inl refl , (λ { _ (inl refl) → self _ ; _ (inr refl) → le i })
