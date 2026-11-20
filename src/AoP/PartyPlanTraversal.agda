{-# OPTIONS --safe --without-K #-}
module AoP.PartyPlanTraversal where

open import AoP.Prelude
open import AoP.Party using (module Planning)
open import AoP.Polynomial using (_⊎_)
open import AoP.Trees using (Rose; Forest; fork; grow; null)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Exercise 7.44. Count case analyses, including on empty forests.
-- Extracting a list from ANY feasible plan visits exactly as many
-- constructors as there are in the input representation. This also
-- applies when few (or no) employees are invited.
module Law {E S : Set} (rating : E → S) (z : S) (add : S → S → S) (R : S → S → Set)
  (rid : ∀ a → R a a) (tr : ∀ {x y z} → R x y → R y z → R x z)
  (mono : ∀ {a b c d} → R a b → R c d → R (add a c) (add b d))
  (cmp : ∀ x y → R x y ⊎ R y x) where
  open Planning rating z add R rid tr mono cmp
  mutual
    nodes : Rose E → Nat
    nodes (fork _ ts) = suc (links ts)
    links : Forest E → Nat
    links null = 1
    links (grow t ts) = suc (nodes t + links ts)
  mutual
    visits : ∀ {p t} → Plan p t → Nat
    visits (invite g) = suc (steps g)
    visits (omit g) = suc (steps g)
    steps : ∀ {p ts} → Guests p ts → Nat
    steps none = 1
    steps (join v vs) = suc (visits v + steps vs)
  mutual
    exact : ∀ {p t} (v : Plan p t) → visits v ≡ nodes t
    exact (invite g) = cong suc (exactᶠ g)
    exact (omit g) = cong suc (exactᶠ g)
    exactᶠ : ∀ {p ts} (g : Guests p ts) → steps g ≡ links ts
    exactᶠ none = refl
    exactᶠ (join v vs) rewrite exact v | exactᶠ vs = refl
