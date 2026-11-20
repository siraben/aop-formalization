{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PairInput where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter05.RelationalPairing using (pair)
open import AoP.Chapter04.Shunting using (Id; graph)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 5.9. Moving an input function inside both branches of a
-- pairing preserves the shared value: both branches start at f x.
module Law {A B C D : Set} (R : C ← B) (S : D ← B) (f : A → B) where
  push : pair R S ∘ graph f ⊆ pair (R ∘ graph f) (S ∘ graph f)
  push {c , d} (b , (r , s) , eq) = (b , r , eq) , (b , s , eq)
  pull : pair (R ∘ graph f) (S ∘ graph f) ⊆ pair R S ∘ graph f
  pull {c , d} ((b , r , refl) , (.b , s , refl)) = b , (r , s) , refl

-- If the input can choose either Boolean, two independent runs can
-- disagree. Sharing one run and duplicating its result cannot produce
-- the mixed pair (true,false).
choice : Bool ← ⊤
choice _ _ = ⊤
apart : pair (Id ∘ choice) (Id ∘ choice) (true , false) tt
apart = (true , refl , tt) , false , refl , tt
shared-impossible : (pair Id Id ∘ choice) (true , false) tt → ⊥
shared-impossible (.true , (refl , ()) , _)
