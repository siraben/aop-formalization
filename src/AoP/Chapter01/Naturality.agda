{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.Naturality where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Inverses using (zip)
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; foldl)
private variable A B C D : Set

-- §1.6: changing labels commutes with each structural list operation.
infixr 6 _++_
_++_ : List A → List A → List A
xs ++ ys = ⦅ ys ∣ _∷_ ⦆ xs

map-++ : (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f [] ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

concat : List (List A) → List A
concat = ⦅ [] ∣ _++_ ⦆

concat-natural : (f : A → B) (xss : List (List A)) →
                 map f (concat xss) ≡ concat (map (map f) xss)
concat-natural f [] = refl
concat-natural f (xs ∷ xss) = begin
  map f (xs ++ concat xss)
    ≡⟨ map-++ f xs (concat xss) ⟩
  map f xs ++ map f (concat xss)
    ≡⟨ cong (map f xs ++_) (concat-natural f xss) ⟩
  concat (map (map f) (xs ∷ xss)) ∎

reverse : List A → List A
reverse = ⦅ [] ∣ (λ x ys → ys ++ (x ∷ [])) ⦆

reverse-natural : (f : A → B) (xs : List A) → map f (reverse xs) ≡ reverse (map f xs)
reverse-natural f [] = refl
reverse-natural f (x ∷ xs) = begin
  map f (reverse xs ++ (x ∷ []))
    ≡⟨ map-++ f (reverse xs) (x ∷ []) ⟩
  map f (reverse xs) ++ (f x ∷ [])
    ≡⟨ cong (_++ (f x ∷ [])) (reverse-natural f xs) ⟩
  reverse (map f (x ∷ xs)) ∎

cross : (A → B) → (C → D) → A × C → B × D
cross f g (x , y) = f x , g y

zip-natural : (f : A → B) (g : C → D) (xs : List A) (ys : List C) →
              map (cross f g) (zip xs ys) ≡ zip (map f xs) (map g ys)
zip-natural f g [] ys = refl
zip-natural f g (x ∷ xs) [] = refl
zip-natural f g (x ∷ xs) (y ∷ ys) = cong ((f x , g y) ∷_) (zip-natural f g xs ys)

mapₗ : (A → B) → Snoc A → Snoc B
mapₗ f = foldl ε (λ ys x → ys ▻ f x)

-- Prefixes include the empty and full lists. Snoc exposes the last prefix
-- directly, so extending the input requires just one new prefix.
inits : Snoc A → Snoc (Snoc A)
inits ε = ε ▻ ε
inits (xs ▻ x) = inits xs ▻ (xs ▻ x)

inits-natural : (f : A → B) (xs : Snoc A) → mapₗ (mapₗ f) (inits xs) ≡ inits (mapₗ f xs)
inits-natural f ε = refl
inits-natural f (xs ▻ x) = cong (_▻ (mapₗ f xs ▻ f x)) (inits-natural f xs)
