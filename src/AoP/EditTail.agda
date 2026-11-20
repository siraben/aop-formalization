{-# OPTIONS --safe --without-K #-}
module AoP.EditTail where

open import AoP.Prelude
open import AoP.EditScript
open import AoP.ConversionCost using (len)
open import AoP.NatOrder using (_≤_; rid; s≤; weaken)

-- Exercise 9.7. Shorten the target string by one letter without
-- changing the source or increasing the number of script operations.
module Law {A : Set} where
  open Scripts {A}
  tail-script : ∀ es x b y → edit es ≡ (x , b ∷ y) →
                Σ (List (Op A)) λ fs → (edit fs ≡ (x , y)) × (len fs ≤ len es)
  tail-script [] x b y ()
  tail-script (copy a ∷ es) _ _ _ refl = (delete a ∷ es) , refl , rid _
  tail-script (insert a ∷ es) _ _ _ refl = es , refl , weaken (rid _)
  tail-script (delete a ∷ es) x b y e with edit es in src | e
  ... | u , .(b ∷ y) | refl with tail-script es u b y src
  ...   | fs , eq , le = (delete a ∷ fs) , cong (step (delete a)) eq , s≤ le
