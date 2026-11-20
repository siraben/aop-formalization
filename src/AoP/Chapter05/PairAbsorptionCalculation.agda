{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PairAbsorptionCalculation where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter05.RelationalProducts using (_⊗_)
open import AoP.Chapter05.RelationalPairing using (pair)

-- §5.2, the staged reverse inclusion in (5.3). Keep the two one-sided
-- rules as arguments, so their combination cannot appeal to tensor
-- composition (the law which absorption is intended to establish).
module Steps {A B C D I : Set} (R : B ← A) (S : D ← C)
  (X : A ← I) (Y : C ← I)
  (pull-left : pair (R ∘ X) (S ∘ Y) ⊆ (R ⊗ Id) ∘ pair X (S ∘ Y))
  (pull-right : pair X (S ∘ Y) ⊆ (Id ⊗ S) ∘ pair X Y) where

  -- Successive coordinate changes keep different coordinates fixed.
  -- Eliminate the two identity edges to obtain the combined change.
  combine : (R ⊗ Id) ∘ (Id ⊗ S) ⊆ R ⊗ S
  combine ((_ , _) , (r , refl) , refl , s) = r , s

  absorb : pair (R ∘ X) (S ∘ Y) ⊆ (R ⊗ S) ∘ pair X Y
  absorb edges with pull-left edges
  ... | u , l , pending with pull-right pending
  ... | v , r , old = v , combine (u , l , r) , old

-- The two witnesses in an edge of the composite pair are the old
-- coordinates. Put back one at a time to instantiate (5.4) and (5.5).
module Relation {A B C D I : Set} (R : B ← A) (S : D ← C) (X : A ← I) (Y : C ← I) where
  left : pair (R ∘ X) (S ∘ Y) ⊆ (R ⊗ Id) ∘ pair X (S ∘ Y)
  left ((a , r , x) , sy) = (a , _) , (r , refl) , x , sy
  right : pair X (S ∘ Y) ⊆ (Id ⊗ S) ∘ pair X Y
  right (x , (c , s , y)) = (_ , c) , (refl , s) , x , y
  open Steps R S X Y left right public using (absorb)
