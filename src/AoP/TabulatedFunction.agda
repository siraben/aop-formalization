{-# OPTIONS --safe --without-K #-}
module AoP.TabulatedFunction where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (graph; Id; Map)

-- Exercises 4.21–23. A table has a source column g and a target
-- column f. If the table describes a function, each input determines
-- exactly one row: totality supplies a row and simplicity identifies
-- its target. Joint injectivity of the columns then identifies the row.
module Columns {A B T : Set} (f : T → B) (g : T → A) where
  span = graph f ∘ graph g ˘
  edge : ∀ t → span (f t) (g t)
  edge t = t , refl , refl

  monic : (∀ x y → f x ≡ f y → g x ≡ g y → x ≡ y) → span ∘ span ˘ ⊆ Id →
          ∀ x y → g x ≡ g y → x ≡ y
  monic joint simple x y eq = joint x y (simple (g x , edge x , y , refl , back eq)) eq
    where back : ∀ {u v : A} → u ≡ v → v ≡ u
          back refl = refl

  module Total (entire : Id ⊆ span ˘ ∘ span) where
    row-for : ∀ a → Σ T (λ t → g t ≡ a)
    row-for a with entire {a} {a} refl
    ... | b , (t , _ , at-a) , _ = t , at-a

    onto : Id ⊆ graph g ∘ graph g ˘
    onto {a} refl with row-for a
    ... | t , eq = t , eq , eq

    diagonal : graph g ∘ graph g ˘ ⊆ Id
    diagonal (_ , refl , refl) = refl

    inverse : A → T
    inverse a = fst (row-for a)
    section : ∀ a → g (inverse a) ≡ a
    section a = snd (row-for a)
    retract : (∀ x y → f x ≡ f y → g x ≡ g y → x ≡ y) → span ∘ span ˘ ⊆ Id →
              ∀ t → inverse (g t) ≡ t
    retract joint simple t = monic joint simple _ t (section (g t))
