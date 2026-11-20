{-# OPTIONS --safe --without-K #-}
module AoP.PolynomialChoices where

open import AoP.Prelude
open import AoP.Polynomial using (Poly; I; K; _⊗_; _⊕_; ⟦_⟧; inl; inr)
open import AoP.Horner using (map)
open import AoP.Naturality using (_++_)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 8.19. Each list at a variable position is a menu. List
-- all ways to fill the positions independently, preserving constants
-- and the input tag. Products use the left menu as the outer loop.
cross : ∀ {A B : Set} → List A → List B → List (A × B)
cross [] ys = []
cross (x ∷ xs) ys = map (x ,_) ys ++ cross xs ys

listcp : ∀ F {A : Set} → ⟦ F ⟧ (List A) → List (⟦ F ⟧ A)
listcp I xs = xs
listcp (K C) c = c ∷ []
listcp (F ⊗ G) (x , y) = cross (listcp F x) (listcp G y)
listcp (F ⊕ G) (inl x) = map inl (listcp F x)
listcp (F ⊕ G) (inr y) = map inr (listcp G y)

-- A nonlinear product already explains the difficulty with (8.11):
-- the middle two outputs of two independent sorted Boolean menus
-- cross in opposite directions under componentwise comparison.
menu : List Bool
menu = false ∷ true ∷ []
example : listcp (I ⊗ I) (menu , menu) ≡ (false , false) ∷ (false , true) ∷ (true , false) ∷ (true , true) ∷ []
example = refl
