{-# OPTIONS --safe --without-K #-}
module AoP.BracketEnumeration where

open import AoP.Prelude
open import AoP.Trees using (Tree; tip; bin)
open import AoP.BracketSpine
open import AoP.Complement using (⊥)
open import AoP.Horner using (map)
open import AoP.Naturality using (concat; _++_)
open import AoP.ListProduct using (collect; locate)
open import AoP.Subsequences using (_∈_; here; there; preimage)
private variable A : Set

-- Every bracketing of a nonempty operand sequence is either a single
-- tip or an insertion into a bracketing of the tail. Recurse on the
-- input sequence, so termination needs no bound on tree shapes.
enumerate : List A → List (Tree A)
enumerate [] = []
enumerate (a ∷ []) = tip a ∷ []
enumerate (a ∷ b ∷ xs) = concat (map (options a) (enumerate (b ∷ xs)))

placed : (a : A) (t : Tree A) {u : Tree A} → u ∈ options a t → Place a t u
placed a (tip x) here = root
placed a (tip x) (there ())
placed a (bin l r) here = root
placed a (bin l r) (there m) with preimage (λ u → bin u r) (options a l) m
... | u , p , refl = descend (placed a l p)

sound⁺ : (a : A) (xs : List A) {t : Tree A} → t ∈ enumerate (a ∷ xs) → leaves t ≡ a ∷ xs
sound⁺ a [] here = refl
sound⁺ a [] (there ())
sound⁺ a (b ∷ xs) q with locate (options a) (enumerate (b ∷ xs)) q
... | t , m , p = preserves (placed a t p) ∙ cong (a ∷_) (sound⁺ b xs m)

sound : (xs : List A) {t : Tree A} → t ∈ enumerate xs → leaves t ≡ xs
sound (a ∷ xs) = sound⁺ a xs

private
  nonempty : (t : Tree A) → Σ A λ a → Σ (List A) λ xs → leaves t ≡ a ∷ xs
  nonempty (tip a) = a , [] , refl
  nonempty (bin l r) with nonempty l
  ... | a , xs , eq = a , xs ++ leaves r , cong (_++ leaves r) eq

  cons-inj : ∀ {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → (x ≡ y) × (xs ≡ ys)
  cons-inj refl = refl , refl

  back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  back refl = refl

complete⁺ : (a : A) (xs : List A) (t : Tree A) → leaves t ≡ a ∷ xs → t ∈ enumerate (a ∷ xs)
complete⁺ a .[] (tip .a) refl = here
complete⁺ a [] (bin l r) eq with peel l r
... | j , t , p with nonempty t
...   | b , tail , ne with snd (cons-inj (back eq ∙ preserves p ∙ cong (j ∷_) ne))
...     | ()
complete⁺ a (b ∷ xs) (bin l r) eq with peel l r
... | j , t , p with cons-inj (back (preserves p) ∙ eq)
...   | refl , ne = collect (options a) (complete⁺ b xs t ne) (occurs p)

complete : (xs : List A) (t : Tree A) → leaves t ≡ xs → t ∈ enumerate xs
complete [] t eq with nonempty t
... | a , xs , ne with back eq ∙ ne
...   | ()
complete (a ∷ xs) = complete⁺ a xs
