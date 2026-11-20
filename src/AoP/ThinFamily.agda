{-# OPTIONS --safe --without-K #-}
module AoP.ThinFamily where

open import AoP.Prelude
open import AoP.Relations using (_←_)
open import AoP.Thinning using (Thin; thin; Pred)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 8.7. For each member of either union, use a matching
-- component in the other family; the two matches need not be inverses.
module Law {I J A : Set} (Q : A ← A) (X : I → Pred A) (Y : J → Pred A) where
  unite : (∀ i → Σ J λ j → Thin Q (X i) (Y j)) →
          (∀ j → Σ I λ i → Thin Q (X i) (Y j)) →
          Thin Q (λ a → Σ I λ i → X i a) (λ a → Σ J λ j → Y j a)
  unite back forth = thin subset cover
    where subset : ∀ {a} → (Σ I λ i → X i a) → Σ J λ j → Y j a
          subset (i , x) with back i
          ... | j , t = j , Thin.subset t x
          cover : ∀ b → (Σ J λ j → Y j b) → Σ A λ a → (Σ I λ i → X i a) × Q a b
          cover b (j , y) with forth j
          ... | i , t with Thin.cover t b y
          ...   | a , x , edge = a , (i , x) , edge

-- Conversely, unite {false} and {true}. Universal comparison lets
-- {false} cover that whole union. But any local thinning of {true}
-- must retain true, so the union of local thinnings cannot be {false}.
module Counterexample where
  Q : Bool ← Bool
  Q _ _ = ⊤
  Y : Bool → Pred Bool
  Y j b = j ≡ b
  global : Thin Q (λ b → b ≡ false) (λ b → Σ Bool λ j → Y j b)
  global = thin (λ { refl → false , refl }) λ b _ → false , refl , tt

  impossible : ∀ {I : Set} (X : I → Pred Bool) →
    (∀ j → Σ I λ i → Thin Q (X i) (Y j)) → (∀ i b → X i b → b ≡ false) → ⊥
  impossible X forth only with forth true
  ... | i , t with Thin.cover t true refl
  ...   | a , kept , _ with Thin.subset t kept
  ...     | refl with only i true kept
  ...       | ()
