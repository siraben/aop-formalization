{-# OPTIONS --safe --without-K #-}
module AoP.ThinIdentity where

open import AoP.Prelude
open import AoP.Thinning using (Pred; Thin; thin)
open import AoP.Power using (_≐_)

-- Exercise 8.1. When candidates dominate only themselves, the
-- coverage witness for each input is that same element in the output.
-- Hence thinning by identity preserves every member in both directions.
preserve : ∀ {A} {X Y : Pred A} → Thin _≡_ X Y → X ≐ Y
preserve t = (λ _ → Thin.subset t) , back
  where back : ∀ y → _ → _
        back y member with Thin.cover t y member
        ... | .y , retained , refl = retained

realize : ∀ {A} {X Y : Pred A} → X ≐ Y → Thin _≡_ X Y
realize (forward , back) = thin (forward _) λ y member → y , back y member , refl
