{-# OPTIONS --safe --without-K #-}
module AoP.Average where

open import AoP.Prelude
open import AoP.Folds
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- §3.1. To average a list, compute its sum and length in one traversal.
-- Keep the answer as an exact ratio. The empty list has average zero,
-- represented by 0/1, so evaluation never returns a zero denominator.
Summary = Nat × Nat
Layer : Set → Set
Layer X = ⊤ ⊎ (Nat × X)

map-layer : ∀ {X Y} → (X → Y) → Layer X → Layer Y
map-layer f (inl u) = inl u
map-layer f (inr (n , x)) = inr (n , f x)

add count : Layer Nat → Nat
add (inl _) = 0
add (inr (a , n)) = a + n
count (inl _) = 0
count (inr (_ , n)) = suc n

combined : Layer Summary → Summary
combined (inl _) = 0 , 0
combined (inr (a , s , n)) = a + s , suc n

-- Exercise 3.1. The paired algebra returns two zeros on nil and
-- updates both coordinates on cons. Check each constructor explicitly.
layer-law : ∀ t → (add (map-layer fst t) , count (map-layer snd t)) ≡ combined t
layer-law (inl _) = refl
layer-law (inr _) = refl

stats : List Nat → Summary
stats = ⦅ (0 , 0) ∣ (λ a p → combined (inr (a , p))) ⦆

split : ∀ xs → (⦅ 0 ∣ _+_ ⦆ xs , ⦅ 0 ∣ (λ _ n → suc n) ⦆ xs) ≡ stats xs
split = banana-split 0 _+_ 0 (λ _ n → suc n)

ratio : Summary → Nat × Nat
ratio (_ , zero) = 0 , 1
ratio (s , suc n) = s , suc n

average : List Nat → Nat × Nat
average xs = ratio (stats xs)

example : average (2 ∷ 3 ∷ 5 ∷ []) ≡ (10 , 3)
example = refl
