{-# OPTIONS --safe --without-K #-}
module AoP.Permutations where

open import AoP.Prelude
open import AoP.Folds
open import AoP.Horner using (map)
open import AoP.Naturality using (concat)
open import AoP.Subsequences using (_∈_; here; there; image; preimage)
open import AoP.ListProduct using (collect; locate)
private variable A : Set

-- §5.6. How do we enumerate all orders of a bag represented by a list?
-- For [a,b,c], first permute [b,c], then insert a at each possible gap.
-- Equal elements may give duplicate outputs: the specification says which
-- lists can appear, not how many distinct lists the algorithm produces.
data Insert (a : A) : List A → List A → Set where
  front : ∀ {xs} → Insert a xs (a ∷ xs)
  later : ∀ {x xs ys} → Insert a xs ys → Insert a (x ∷ xs) (x ∷ ys)

places : A → List A → List (List A)
places a [] = (a ∷ []) ∷ []
places a (x ∷ xs) = (a ∷ x ∷ xs) ∷ map (x ∷_) (places a xs)

place-complete : ∀ {a : A} {xs ys} → Insert a xs ys → ys ∈ places a xs
place-complete (front {[]}) = here
place-complete (front {_ ∷ _}) = here
place-complete (later p) = there (image (_ ∷_) (place-complete p))

place-sound : (a : A) (xs : List A) {ys : List A} → ys ∈ places a xs → Insert a xs ys
place-sound a [] here = front
place-sound a [] (there ())
place-sound a (x ∷ xs) here = front
place-sound a (x ∷ xs) (there m) with preimage (x ∷_) (places a xs) m
... | zs , q , refl = later (place-sound a xs q)

data Perm {A : Set} : List A → List A → Set where
  empty : Perm [] []
  insert : ∀ {a xs ys zs} → Perm xs ys → Insert a ys zs → Perm (a ∷ xs) zs

perms : List A → List (List A)
perms = ⦅ ([] ∷ []) ∣ (λ a yss → concat (map (places a) yss)) ⦆

complete : ∀ {xs ys : List A} → Perm xs ys → ys ∈ perms xs
complete empty = here
complete (insert {a} p i) = collect (places a) (complete p) (place-complete i)

sound : (xs : List A) {ys : List A} → ys ∈ perms xs → Perm xs ys
sound [] here = empty
sound [] (there ())
sound (a ∷ xs) m with locate (places a) (perms xs) m
... | zs , p , q = insert (sound xs p) (place-sound a zs q)
