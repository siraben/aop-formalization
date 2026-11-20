{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.EditDropSquares where

open import AoP.Common.Prelude
open import AoP.Chapter09.EditScript
open import AoP.Chapter09.EditSuffix using (module Target)
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)
open import AoP.Chapter04.Shunting using (graph)

-- Exercise 9.7. Push the target-tail relation inwards through one
-- decoder layer. Insertion disappears, copy becomes deletion, and
-- deletion commutes with the pending tail. These local calculations
-- depend only on endpoint pairs, not on the rest of the script.
module Squares {A : Set} where
  open Scripts {A} using (Strings; step)
  open Target {A} using (Drop; drop)
  Layer : Op A → Strings ← Strings
  Layer op = graph (step op)
  Id : Strings ← Strings
  Id p q = p ≡ q

  insert-square : ∀ a → Drop ∘ Layer (insert a) ⊆ Id
  insert-square a {a = x , y} (_ , drop , refl) = refl
  copy-square : ∀ a → Drop ∘ Layer (copy a) ⊆ Layer (delete a)
  copy-square a {a = x , y} (_ , drop , refl) = refl
  delete-square : ∀ a → Drop ∘ Layer (delete a) ⊆ Layer (delete a) ∘ Drop
  delete-square a {a = x , b ∷ y} (_ , drop , refl) = (x , y) , refl , drop
