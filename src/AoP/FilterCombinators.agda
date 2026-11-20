{-# OPTIONS --safe --without-K #-}
module AoP.FilterCombinators where

open import AoP.Prelude
open import AoP.Horner using (map)
open import AoP.Inverses using (zip)

-- §1.7, (1.3)–(1.5) and (1.7). The two maps start from the same
-- spine, so zip can neither truncate nor misalign their results.
private variable A B C : Set

nilp : A → List B
nilp _ = []
wrap : A → List A
wrap a = a ∷ []

constant-empty : (f : A → B) (a : A) → nilp {B = C} (f a) ≡ nilp a
constant-empty f a = refl
map-empty : (f : A → B) (x : C) → map f (nilp x) ≡ nilp x
map-empty f x = refl
map-wrap : (f : A → B) (a : A) → map f (wrap a) ≡ wrap (f a)
map-wrap f a = refl

zip-pair : (f : A → B) (g : A → C) (xs : List A) → zip (map f xs) (map g xs) ≡ map (λ a → f a , g a) xs
zip-pair f g [] = refl
zip-pair f g (a ∷ xs) = cong ((f a , g a) ∷_) (zip-pair f g xs)
