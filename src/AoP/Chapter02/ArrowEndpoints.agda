{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ArrowEndpoints where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories using (Category)
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 2.2. Read composition right to left. Starting at A,
-- h, f, h, k trace A → B → A → B → C.
module Interpret {o h₀ e} (K : Category o h₀ e) where
  open Category K
  composite : ∀ {A B C} → Hom B A → Hom A B → Hom B C → Hom A C
  composite f h k = k ∘ h ∘ f ∘ h

-- For g ∘ k ∘ h the last step instead starts at A, while k has
-- just reached C. Model the distinct labels explicitly so failure
-- to match endpoints is a proposition with a checked negation.
data Node : Set where A B C : Node
data Arrow : Set where f g h k : Arrow
source target : Arrow → Node
source f = B
source g = A
source h = A
source k = B
target f = A
target g = C
target h = B
target k = C

bad : (target h ≡ source k) × (target k ≡ source g) → ⊥
bad (_ , ())
