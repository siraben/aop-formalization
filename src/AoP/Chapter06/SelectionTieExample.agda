{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SelectionTieExample where

open import AoP.Common.Prelude
open import AoP.Chapter06.ConnectedSelectionSort using (module Sort)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)

-- Two distinguishable records have the same priority. Either direction
-- is a valid comparison. The sorting contract retains both records;
-- preserving their arrival order requires more from the comparison.
data Ticket : Set where first second : Ticket
Tied : Ticket → Ticket → Set
Tied _ _ = ⊤
left right : ∀ x y → Tied x y ⊎ Tied y x
left _ _ = inl tt
right _ _ = inr tt
module L = Sort Tied (λ _ _ → tt) left
module R = Sort Tied (λ _ _ → tt) right

keep-order : fst (L.sort (first ∷ second ∷ [])) ≡ first ∷ second ∷ []
keep-order = refl
swap-order : fst (R.sort (first ∷ second ∷ [])) ≡ second ∷ first ∷ []
swap-order = refl
