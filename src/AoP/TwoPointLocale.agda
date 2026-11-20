{-# OPTIONS --safe --without-K #-}
module AoP.TwoPointLocale where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 4.25: the opens of a discrete two-point space are two
-- independent truth values. Use small predicates, ordered by pointwise
-- implication. The grade carrier itself lives in Set₁; all joins here
-- are indexed by small types. No decision of inhabitation is needed.
Grade : Set₁
Grade = Bool → Set
_≤_ : Grade → Grade → Set
U ≤ V = ∀ p → U p → V p
meet : Grade → Grade → Grade
meet U V p = U p × V p
join : ∀ {I : Set} → (I → Grade) → Grade
join {I} U p = Σ I λ i → U i p

distribute : ∀ {I : Set} (U : I → Grade) V → meet (join U) V ≤ join (λ i → meet (U i) V)
distribute U V p ((i , u) , v) = i , u , v

-- A total leg X → 1 has a witness in each coordinate at every x.
-- Unfolding diagonal ⊆ f° ∘ f gives this fact at (x,x) directly.
Leg : Set → Set₁
Leg X = X → Grade
Total : ∀ {X} → Leg X → Set
Total f = ∀ x p → f x p
span : ∀ {X} → Leg X → Leg X → Grade
span f g = join (λ x → meet (f x) (g x))

one-point : Grade
one-point false = ⊤
one-point true = ⊥

-- Factoring the one-point open at false supplies an actual x. Both
-- legs at x must also hold at true; factorization there contradicts ⊥.
no-span : ∀ {X} (f g : Leg X) → Total f → Total g → one-point ≤ span f g → span f g ≤ one-point → ⊥
no-span f g tf tg into out with into false tt
... | x , _ = out true (x , tf x true , tg x true)
