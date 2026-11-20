{-# OPTIONS --safe --without-K #-}
module AoP.BusReference where

open import AoP.Prelude
open import AoP.BusWalking using (module Layout; trips)
open import AoP.BusLayouts using (Layout; layouts; complete; sound)
open import AoP.ConversionCost using (len)
open import AoP.FiniteMinimum using (module Search)
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (inl; inr)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat)

-- Reference search for exercise 8.31: test all exact-size layouts
-- and certify a minimum against the layout specification. A service
-- requires a boarding stop, even when the demand list is empty.
module Plan (blocks : List (Nat × Nat)) (quota : Nat) where
  Serves : List Nat → Set
  Serves [] = ⊥
  Serves (_ ∷ _) = ⊤
  cost : List Nat → Nat
  cost [] = 0  -- excluded by Serves
  cost (x ∷ xs) = Layout.walking x xs 0 blocks
  module M = Search Serves (λ { [] → inr (λ p → p) ; (_ ∷ _) → inl tt }) cost
  Legal : List Nat → Set
  Legal xs = Layout 0 (len blocks) quota xs × Serves xs
  data Answer : Set where
    impossible : (∀ xs → Legal xs → ⊥) → Answer
    best : (xs : List Nat) → Legal xs → (∀ ys → Legal ys → cost xs ≤ cost ys) → Answer
  solve : Answer
  solve with M.scan (layouts 0 (len blocks) quota)
  ... | M.none no = impossible λ xs g → no xs (complete (fst g)) (snd g)
  ... | M.best xs m ok opt = best xs (sound 0 _ _ m , ok) λ ys g → opt ys (complete (fst g)) (snd g)

module Example = Plan trips 2
chosen : Example.Answer → List Nat
chosen (Example.impossible _) = []
chosen (Example.best xs _ _) = xs
example : chosen Example.solve ≡ 0 ∷ 2 ∷ []
example = refl
