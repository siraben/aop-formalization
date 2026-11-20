{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.AccessibilityMeasure where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter06.Inductive using (Acc; acc)

-- Exercise 6.16. A function measures each state in a well-founded
-- space. Pulling the comparison back measures every possible child
-- by the very same function, even if distinct states share a measure.
module Measure {A B : Set} (f : A → B) (R : B ← B) where
  Pull : A ← A
  Pull y x = R (f y) (f x)

  descend : ∀ {m} → Acc R m → (x : A) → m ≡ f x → Acc Pull x
  descend (acc smaller) x refl = acc λ y edge → descend (smaller (f y) edge) y refl

  well-founded : (∀ m → Acc R m) → ∀ x → Acc Pull x
  well-founded wf x = descend (wf (f x)) x refl
