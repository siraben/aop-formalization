{-# OPTIONS --safe --without-K #-}
module AoP.TensorFactorCalculation where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_)
open import AoP.Shunting using (graph; Id)
open import AoP.RelationalPairing using (pair)

-- Exercise 5.6. Keep the tensor opaque throughout the calculation.
-- Use the two directions of (5.2) separately so the proof works with
-- extensional equality of relations. The only other product law needed
-- is (5.4), moving a left-component action outside a pairing.
module Laws (_×r_ : ∀ {A B C D} → B ← A → D ← C → (B × D) ← (A × C))
  (expand : ∀ {A B C D} (R : B ← A) (S : D ← C) → (R ×r S) ⊆ pair (R ∘ graph fst) (S ∘ graph snd))
  (contract : ∀ {A B C D} (R : B ← A) (S : D ← C) → pair (R ∘ graph fst) (S ∘ graph snd) ⊆ (R ×r S))
  (pull : ∀ {A B C D} (R : B ← A) (X : A ← C) (Y : D ← C) → pair (R ∘ X) Y ⊆ (R ×r Id) ∘ pair X Y) where

  factor : ∀ {A B C D} (R : B ← A) (S : D ← C) → (R ×r S) ⊆ (R ×r Id) ∘ (Id ×r S)
  factor {A} {B} {C} {D} R S edge with pull R (graph fst) (S ∘ graph snd) (expand R S edge)
  ... | mid , r , x , y = mid , r , contract Id S ((_ , refl , x) , y)

-- Instantiate the named laws without relying on tensor composition.
open import AoP.RelationalProducts using (_⊗_)
private
  expand : ∀ {A B C D} (R : B ← A) (S : D ← C) → (R ⊗ S) ⊆ pair (R ∘ graph fst) (S ∘ graph snd)
  expand R S (r , s) = (_ , r , refl) , (_ , s , refl)
  contract : ∀ {A B C D} (R : B ← A) (S : D ← C) → pair (R ∘ graph fst) (S ∘ graph snd) ⊆ (R ⊗ S)
  contract R S ((_ , r , refl) , (_ , s , refl)) = r , s
  pull : ∀ {A B C D} (R : B ← A) (X : A ← C) (Y : D ← C) → pair (R ∘ X) Y ⊆ (R ⊗ Id) ∘ pair X Y
  pull R X Y ((x , r , u) , v) = (x , _) , (r , refl) , u , v

module Concrete = Laws _⊗_ expand contract pull
