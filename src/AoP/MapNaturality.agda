{-# OPTIONS --safe --without-K #-}
module AoP.MapNaturality where

open import AoP.Prelude
open import AoP.Horner using (map)
open import AoP.Functors using (map-comp)
private variable A B C D : Set

-- Exercise 3.38. The source bifunctor assigns to (A,B) the functions
-- A → B; the target assigns List A → List B. Both act contravariantly
-- on the input and covariantly on the output. The map component turns
-- an element function into a list function. Moving an input conversion
-- and an output conversion across this component gives the square below.
transport : (C → A) → (B → D) → (A → B) → C → D
transport pre post f x = post (f (pre x))

natural : (pre : C → A) (post : B → D) (f : A → B) (xs : List C) →
          map (transport pre post f) xs ≡ transport (map pre) (map post) (map f) xs
natural pre post f xs = begin
  map (transport pre post f) xs ≡⟨ map-comp post (λ x → f (pre x)) xs ⟩
  map post (map (λ x → f (pre x)) xs) ≡⟨ cong (map post) (map-comp f pre xs) ⟩
  map post (map f (map pre xs)) ∎
