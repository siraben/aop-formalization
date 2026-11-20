{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.MeetWitness where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 4.3. Forget a Boolean intermediate value. Starting at tt,
-- S can choose true and T can choose false. Both paths finish at tt,
-- but no single intermediate value works for both S and T.
R : ⊤ ← Bool
R _ _ = ⊤
S T : Bool ← ⊤
S b _ = b ≡ true
T b _ = b ≡ false

paths : ((R ∘ S) ⊓ (R ∘ T)) tt tt
paths = (true , tt , refl) , (false , tt , refl)

impossible : (R ∘ (S ⊓ T)) tt tt → ⊥
impossible (true , _ , _ , ())
impossible (false , _ , () , _)

counterexample : ((R ∘ S) ⊓ (R ∘ T) ⊆ R ∘ (S ⊓ T)) → ⊥
counterexample inclusion = impossible (inclusion paths)

-- The forward distribution inclusion always works: reuse the same
-- intermediate value for both paths.
distribute : ∀ {A B C : Set} (r : C ← B) (s t : B ← A) →
             r ∘ (s ⊓ t) ⊆ (r ∘ s) ⊓ (r ∘ t)
distribute r s t (b , rb , sb , tb) = (b , rb , sb) , (b , rb , tb)
