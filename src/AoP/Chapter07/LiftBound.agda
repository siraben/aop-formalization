{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.LiftBound where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter07.ResidualFactor using (module Law)
open import AoP.Chapter05.PowerRelator using (Lift; cover)

-- Exercise 7.4. A lower bound through the power relator needs an
-- intermediate set covered in both directions. Exercise 7.3 gives
-- a bounded set covering every source member. Keep just the elements
-- reached from the source: this adds backward coverage without losing
-- a single forward witness.
module Bound {A B C : Set} (R : C ← B) (S : B ← A) (X : A → Set) where
  module F = Law R S (λ a (_ : ⊤) → X a)

  Lifted : C → Set₁
  Lifted c = Σ (B → Set) λ Y → (∀ b → Y b → R c b) × Lift S Y X

  introduce : ∀ {c} → F.Direct c tt → Lifted c
  introduce {c} direct with F.factor {c} {tt} direct
  ... | Y , bound , reach = Kept , (λ b p → bound b (fst p)) , cover (λ _ → snd) forward
    where
    Kept : B → Set
    Kept b = Y b × (Σ A λ a → X a × S b a)
    forward : ∀ a → X a → Σ B λ b → Kept b × S b a
    forward a xa with reach a xa
    ... | b , y , edge = b , (y , a , xa , edge) , edge

  eliminate : ∀ {c} → Lifted c → F.Direct c tt
  eliminate {c} (Y , bound , lift) = F.compose {c} {tt} (Y , bound , Lift.forward lift)
