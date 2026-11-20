{-# OPTIONS --safe --without-K #-}
module AoP.PartyPairTrace where

open import AoP.Prelude
open import AoP.PartyExample using (Person; Ada; Bo; Cy; rating)
open import AoP.PartyExcludeMaximum using (module Solve)
open Solve rating

-- Reconstruct the two leaf pairs, then the manager's pair. In each
-- pair the first list requires the root to attend and the second
-- requires the root to stay home. Choosing between them is a separate
-- final step; requiring the president uses only the first projection.
leaf : Person → List Person × List Person
leaf e = fst (maximum e [])
bo : leaf Bo ≡ ((Bo ∷ []) , [])
bo = refl
cy : leaf Cy ≡ ((Cy ∷ []) , [])
cy = refl
alternatives = leaf Bo ∷ leaf Cy ∷ []
report-choices : fst (choices alternatives) ≡ (Bo ∷ []) ∷ (Cy ∷ []) ∷ []
report-choices = refl
root = fst (maximum Ada alternatives)
manager : root ≡ ((Ada ∷ []) , (Bo ∷ Cy ∷ []))
manager = refl
best : fst (pick root) ≡ Bo ∷ Cy ∷ []
best = refl
