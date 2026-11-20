{-# OPTIONS --safe --without-K #-}
module AoP.CopairCancellation where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Relations
open import AoP.Complement using (_⊔_)
private variable A B C D : Set

copair : (C ← A) → (C ← B) → C ← (A ⊎ B)
copair R S c (inl a) = R c a
copair R S c (inr b) = S c b

-- Exercise 5.13. A witness for the composite has just one intermediate
-- tag. Reading it determines which summand contributes the path;
-- injecting the witness reconstructs the composite. The product law
-- instead combines two independent paths and requires both witnesses.
module Law (R : C ← A) (S : C ← B) (U : D ← A) (V : D ← B) where
  split : copair R S ∘ copair U V ˘ ⊆ (R ∘ U ˘) ⊔ (S ∘ V ˘)
  split (inl a , r , u) = inl (a , r , u)
  split (inr b , s , v) = inr (b , s , v)

  join : (R ∘ U ˘) ⊔ (S ∘ V ˘) ⊆ copair R S ∘ copair U V ˘
  join (inl (a , r , u)) = inl a , r , u
  join (inr (b , s , v)) = inr b , s , v
