{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PowerMeetFailure where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter05.PowerRelator using (Lift; cover)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 5.2, unrestricted meets. On the whole two-element set,
-- identity covers each bit by itself; negation covers it by the other
-- bit. Both lifts therefore accept the same pair of sets, but their
-- intersection has no edge at all. No common covering witness exists.
flip : Bool → Bool
flip true = false
flip false = true
opposite : Bool ← Bool
opposite b a = flip a ≡ b
whole : Bool → Set
whole _ = ⊤

id-cover : Lift Id whole whole
id-cover = cover (λ b _ → b , tt , refl) (λ a _ → a , tt , refl)
flip-cover : Lift opposite whole whole
flip-cover = cover prev (λ a _ → flip a , tt , refl)
  where prev : ∀ b → whole b → Σ Bool (λ a → whole a × opposite b a)
        prev true _ = false , tt , refl
        prev false _ = true , tt , refl

no-common : Lift (Id ⊓ opposite) whole whole → ⊥
no-common p with Lift.forward p true tt
... | .true , _ , refl , ()

fails : (Lift Id whole whole × Lift opposite whole whole → Lift (Id ⊓ opposite) whole whole) → ⊥
fails preserve = no-common (preserve (id-cover , flip-cover))
