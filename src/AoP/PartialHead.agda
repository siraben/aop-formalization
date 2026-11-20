{-# OPTIONS --safe --without-K #-}
module AoP.PartialHead where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Bool using (Bool; true; false)
private variable A B C : Set

-- Exercise 2.18. A partial list map succeeds only when *every* element
-- has an image. Computing the head first can skip an undefined tail.
bind : Maybe A → (A → Maybe B) → Maybe B
bind nothing f = nothing
bind (just x) f = f x

traverse : (A → Maybe B) → List A → Maybe (List B)
traverse f [] = just []
traverse f (x ∷ xs) = bind (f x) λ y → bind (traverse f xs) λ ys → just (y ∷ ys)

head : List A → Maybe A
head [] = nothing
head (x ∷ _) = just x

only-true : Bool → Maybe Bool
only-true true = just true
only-true false = nothing

input = true ∷ false ∷ []
whole-list : bind (traverse only-true input) head ≡ nothing
whole-list = refl
first-only : bind (head input) only-true ≡ just true
first-only = refl

-- head cannot satisfy the naturality square for all arrows in Par.
refute : (∀ (f : Bool → Maybe Bool) xs → bind (traverse f xs) head ≡ bind (head xs) f) → ⊥
refute law with law only-true input
... | ()
