{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PartitionRanges where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_)
open import AoP.Chapter04.Relations hiding (cons)
open import AoP.Chapter04.Shunting using (graph)
open import AoP.Chapter05.RelationalProducts using (_⊗_)
open import AoP.Chapter04.Shunting using (Id)

-- Exercise 5.25. A partition is a list of nonempty blocks. Starting
-- a new block produces a singleton head; gluing extends a pre-existing
-- head, so the new head has at least two items. The two equations test
-- these shapes while preserving the remaining blocks unchanged.
module Law (A : Set) where
  Block = Nonempty A
  Parts = List Block
  single : A → Block
  single x = x ∷⁺ []
  extend : A × Block → Block
  extend (x , (y ∷⁺ ys)) = x ∷⁺ (y ∷ ys)
  cons : Block × Parts → Parts
  cons (b , bs) = b ∷ bs
  new : A × Parts → Parts
  new (x , bs) = single x ∷ bs
  data Glue : Parts ← (A × Parts) where
    glue : ∀ x b bs → Glue (extend (x , b) ∷ bs) (x , b ∷ bs)

  head-test : ∀ {T : Set} → (T → Block) → Parts ← Parts
  head-test f = graph cons ∘ ((graph f ∘ graph f ˘) ⊗ Id) ∘ graph cons ˘

  new-out : graph new ∘ graph new ˘ ⊆ head-test single
  new-out ((x , bs) , refl , refl) = _ , refl , _ , ((x , refl , refl) , refl) , refl
  new-in : head-test single ⊆ graph new ∘ graph new ˘
  new-in ((b , bs) , refl , (c , cs) , ((x , refl , refl) , refl) , refl) = (x , bs) , refl , refl

  glue-out : Glue ∘ Glue ˘ ⊆ head-test extend
  glue-out (_ , glue x b bs , glue .x .b .bs) = _ , refl , _ , (((x , b) , refl , refl) , refl) , refl
  glue-in : head-test extend ⊆ Glue ∘ Glue ˘
  glue-in ((b , bs) , refl , (c , cs) , (((x , d) , refl , refl) , refl) , refl) = _ , glue x d bs , glue x d bs
