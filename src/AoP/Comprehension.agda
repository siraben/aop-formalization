{-# OPTIONS --safe --without-K #-}
module AoP.Comprehension where

open import AoP.Prelude
open import AoP.Horner using (map)
open import AoP.PointFree using (filter)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)

-- §1.3. A comprehension visits its source in order, decides the guard
-- on the original element, and transforms each survivor. Mapping after
-- filtering gives the same result, including repeated surviving values.
collect : ∀ {A B : Set} → (A → B) → (A → Bool) → List A → List B
collect f p [] = []
collect f p (x ∷ xs) with p x
... | true = f x ∷ collect f p xs
... | false = collect f p xs

map-filter : ∀ {A B : Set} (f : A → B) p xs → collect f p xs ≡ map f (filter p xs)
map-filter f p [] = refl
map-filter f p (x ∷ xs) with p x
... | true = cong (f x ∷_) (map-filter f p xs)
... | false = map-filter f p xs

even : Nat → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

range : Nat → Nat → List Nat
range start zero = []
range start (suc length) = start ∷ range (suc start) length

even-squares : collect (λ n → n * n) even (range 1 10) ≡ 4 ∷ 16 ∷ 36 ∷ 64 ∷ 100 ∷ []
even-squares = refl
