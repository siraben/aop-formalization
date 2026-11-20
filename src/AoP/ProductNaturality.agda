{-# OPTIONS --safe --without-K #-}
module AoP.ProductNaturality where

open import AoP.Prelude
open import AoP.UniversalImage using (Some)
open import AoP.Horner using (map)

-- Exercise 2.16. A menu is a set of choices, represented by a predicate.
-- A sequence belongs to the cartesian product when it chooses exactly one
-- member of each menu in order. The naturality square compares two ways
-- of relabelling choices by f: before choosing, or after choosing.
data Menus (A : Set) : Set₁ where
  nil : Menus A
  cons : (A → Set) → Menus A → Menus A

open import AoP.Complement using (⊥)
Choose : ∀ {A} → Menus A → List A → Set
Choose nil [] = ⊤
Choose nil (_ ∷ _) = ⊥
Choose (cons _ _) [] = ⊥
Choose (cons P ps) (a ∷ xs) = P a × Choose ps xs

images : ∀ {A B : Set} → (A → B) → Menus A → Menus B
images f nil = nil
images f (cons P ps) = cons (Some f P) (images f ps)

-- cp : List ∘ Power ⇒ Power ∘ List, with direct image on subsets.
-- The backwards direction extracts a preimage at every position. These
-- witnesses are already in the premise; finite recursion collects them.
module Square {A B : Set} (f : A → B) where
  relabel : ∀ ps xs → Choose ps xs → Choose (images f ps) (map f xs)
  relabel nil [] _ = tt
  relabel nil (_ ∷ _) ()
  relabel (cons _ _) [] ()
  relabel (cons P ps) (x ∷ xs) (p , rest) = (x , refl , p) , relabel ps xs rest

  forward : ∀ ps ys → Some (map f) (Choose ps) ys → Choose (images f ps) ys
  forward ps _ (xs , refl , choices) = relabel ps xs choices

  backward : ∀ ps ys → Choose (images f ps) ys → Some (map f) (Choose ps) ys
  backward nil [] _ = [] , refl , tt
  backward nil (_ ∷ _) ()
  backward (cons _ _) [] ()
  backward (cons P ps) (_ ∷ ys) ((a , refl , p) , rest) with backward ps ys rest
  ... | xs , refl , original = (a ∷ xs) , refl , p , original
