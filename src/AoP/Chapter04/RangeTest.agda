{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.RangeTest where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter04.RangeRotation using (ran)
private variable A B : Set

-- Exercises 4.10 and 4.12. A successful output test C leaves the
-- output unchanged. Move the test inside an intersection, or test the
-- range after projecting away the input. Both moves keep the witness.
module Restrict (C : B ← B) (core : C ⊆ Id) (R : B ← A) where
  push : (S : B ← A) → (C ∘ R) ⊓ S ⊆ C ∘ (R ⊓ S)
  push S ((b , c , r) , s) with core c
  ... | refl = b , c , r , s

  pull : (S : B ← A) → C ∘ (R ⊓ S) ⊆ (C ∘ R) ⊓ S
  pull S (b , c , r , s) with core c
  ... | refl = (b , c , r) , s

  range-after : ran (C ∘ R) ⊆ C ∘ ran R
  range-after (refl , a , b , c , r) with core c
  ... | refl = b , c , refl , a , r

  range-before : C ∘ ran R ⊆ ran (C ∘ R)
  range-before (b , c , refl , a , r) with core c
  ... | refl = refl , a , b , c , r
