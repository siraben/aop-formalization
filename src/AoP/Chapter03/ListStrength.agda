{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.ListStrength where

open import AoP.Common.Prelude
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter03.Currying using (curry; uncurry)
private variable A B : Set

-- Exercise 3.39. Carry a fixed value along every element of a list.
-- For a list on the right, curry the identity of the product to obtain
-- the section b ↦ (a,b), map that section, then uncurry. The analogous
-- left-list comprehension keeps the second component fixed instead.
_∘_ : ∀ {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(f ∘ g) x = f (g x)

cpr : A × List B → List (A × B)
cpr = uncurry (map ∘ curry (λ p → p))

swap : A × B → B × A
swap (x , y) = y , x

cpl : List A × B → List (A × B)
cpl = uncurry (map ∘ curry swap) ∘ swap

right-cons : (a : A) (b : B) (bs : List B) → cpr (a , b ∷ bs) ≡ (a , b) ∷ cpr (a , bs)
right-cons a b bs = refl
left-cons : (b : B) (a : A) (as : List A) → cpl (a ∷ as , b) ≡ (a , b) ∷ cpl (as , b)
left-cons b a as = refl
