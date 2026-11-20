{-# OPTIONS --safe --without-K #-}
module AoP.Complement where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Polynomial using (_⊎_; inl; inr)
private variable A B C : Set

data ⊥ : Set where

infix 9 ¬_
¬_ : (B ← A) → B ← A
(¬ R) b a = R b a → ⊥

infixr 5 _⊔_
_⊔_ : (B ← A) → (B ← A) → B ← A
(R ⊔ S) b a = R b a ⊎ S b a

antitone : (R S : B ← A) → R ⊆ S → ¬ S ⊆ ¬ R
antitone R S sub ns r = ns (sub r)

module DeMorgan (R S : B ← A) where
  split : ¬ (R ⊔ S) ⊆ ¬ R ⊓ ¬ S
  split n = (λ r → n (inl r)) , (λ s → n (inr s))
  merge : ¬ R ⊓ ¬ S ⊆ ¬ (R ⊔ S)
  merge (nr , ns) (inl r) = nr r
  merge (nr , ns) (inr s) = ns s

-- §4.5, eq. 4.22: no excluded middle is needed to refute a witness.
module Division (R : C ← A) (Y : B ← A) where
  push : (¬ R) ／ Y ⊆ ¬ (R ∘ Y ˘)
  push d (a , r , y) = d y r
  pull : ¬ (R ∘ Y ˘) ⊆ (¬ R) ／ Y
  pull n y r = n (_ , r , y)

-- Eq. 4.21. In the book's boolean setting double negation cancels.
-- Only stability of X is needed for this direction; make it a premise,
-- rather than silently assuming all Agda sets have classical negation.
module BooleanDivision (X : C ← A) (Y : B ← A) where
  forward : X ／ Y ⊆ ¬ ((¬ X) ∘ Y ˘)
  forward d (a , nx , y) = nx (d y)

  backward : ¬ (¬ X) ⊆ X → ¬ ((¬ X) ∘ Y ˘) ⊆ X ／ Y
  backward stable n y = stable (Division.pull (¬ X) Y n y)
