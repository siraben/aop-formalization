{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.StrictInitial where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.UniversalObjects using (module Universal)

-- §3.4, exercises 3.23 and 3.27. In the nullary distribution law the
-- canonical map from 0 to A × 0 is invertible. For the first exercise
-- its inverse is the second projection. Equality on both projections
-- suffices to check the round trip. For the second exercise an arrow
-- from A to 0 lets us pair it with identity and reuse the same triangle.
module Laws {o h e} (C : Category o h e) where
  open Category C
  open Universal C
  module Zero {Z A P : Obj} (initial : Initial Z)
    (l : Hom P A) (r : Hom P Z) where
    open Initial initial
    unnull = leave P
    module Triangle (triangle : leave A ∘ r ≈ l) where
      module Product
        (ext : (f g : Hom P P) → l ∘ f ≈ l ∘ g → r ∘ f ≈ r ∘ g → f ≈ g) where
        undo : r ∘ unnull ≈ identity
        undo = transitive (unique _) (symmetric (unique identity))
        restore : unnull ∘ r ≈ identity
        restore = ext _ identity
          (transitive (symmetric (assoc l unnull r))
            (transitive (compose-cong (unique _) reflexive) (transitive triangle (symmetric (unitʳ l)))))
          (transitive (symmetric (assoc r unnull r))
            (transitive (compose-cong undo reflexive) (transitive (unitˡ r) (symmetric (unitʳ r)))))

      module Strict (h₀ : Hom A Z) (pair : Hom A P)
                    (first : l ∘ pair ≈ identity) (second : r ∘ pair ≈ h₀) where
        invert : leave A ∘ h₀ ≈ identity
        invert = transitive (compose-cong reflexive (symmetric second))
          (transitive (symmetric (assoc (leave A) r pair)) (transitive (compose-cong triangle reflexive) first))
        retract : h₀ ∘ leave A ≈ identity
        retract = transitive (unique _) (symmetric (unique identity))
        inherited : Initial A
        Initial.leave inherited B = leave B ∘ h₀
        Initial.unique inherited f = transitive (symmetric (unitʳ f))
          (transitive (compose-cong reflexive (symmetric invert))
            (transitive (symmetric (assoc f (leave A) h₀)) (compose-cong (unique _) reflexive)))
