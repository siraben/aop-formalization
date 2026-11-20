{-# OPTIONS --safe --without-K #-}
module AoP.PointFree where

open import Agda.Builtin.Bool
open import AoP.Prelude
open import AoP.Horner using (map)
open import AoP.Inverses using (zip)
open import AoP.Naturality using (concat; _++_)
private variable A B : Set

-- §1.7. A selection contributes either a singleton or no elements.
wrapIf : Bool → A → List A
wrapIf true x = x ∷ []
wrapIf false x = []

filter : (A → Bool) → List A → List A
filter p xs = concat (map (λ x → wrapIf (p x) x) xs)

-- Pairing a list with its pointwise image is itself a single map.
zip-map : (f : A → B) (xs : List A) → zip xs (map f xs) ≡ map (λ x → x , f x) xs
zip-map f [] = refl
zip-map f (x ∷ xs) = cong ((x , f x) ∷_) (zip-map f xs)

-- The conditional step lemma is where the boolean case distinction lives;
-- it need not be repeated in the calculation on whole lists.
select-step : (b : Bool) (x : A) (ps : List (A × Bool)) →
  map fst (wrapIf b (x , b) ++ ps) ≡ wrapIf b x ++ map fst ps
select-step true x ps = refl
select-step false x ps = refl

module Selection {A : Set} (p : A → Bool) where
  tag : A → A × Bool
  tag x = x , p x

  project : (xs : List A) → map fst (filter snd (map tag xs)) ≡ filter p xs
  project [] = refl
  project (x ∷ xs) = begin
    map fst (filter snd (map tag (x ∷ xs)))
      ≡⟨ select-step (p x) x (filter snd (map tag xs)) ⟩
    wrapIf (p x) x ++ map fst (filter snd (map tag xs))
      ≡⟨ cong (wrapIf (p x) x ++_) (project xs) ⟩
    filter p (x ∷ xs) ∎

  tagged-filter : (xs : List A) → map fst (filter snd (zip xs (map p xs))) ≡ filter p xs
  tagged-filter xs = begin
    map fst (filter snd (zip xs (map p xs)))
      ≡⟨ cong (λ pairs → map fst (filter snd pairs)) (zip-map p xs) ⟩
    map fst (filter snd (map tag xs))
      ≡⟨ project xs ⟩
    filter p xs ∎
