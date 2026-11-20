{-# OPTIONS --safe --without-K #-}
module AoP.EntireFold where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (Id)

-- Exercise 5.19 for cons-lists. An entire list algebra supplies at
-- least one value for nil and one successor for every head and already
-- reduced tail. Assemble those local witnesses into a successful run
-- of the fold on any input, retaining its derivation as evidence.
module Lists {A B : Set} (E : B → Set) (F : B ← (A × B))
             (base : Σ B E) (step : ∀ a b → Σ B λ c → F c (a , b)) where
  run : ∀ xs → Σ B λ b → Fold E F b xs
  run [] = fst base , nil (snd base)
  run (a ∷ xs) with run xs
  ... | b , tail with step a b
  ...   | c , edge = c , cons edge tail

  entire : Id ⊆ Fold E F ˘ ∘ Fold E F
  entire {xs} refl with run xs
  ... | b , path = b , path , path
