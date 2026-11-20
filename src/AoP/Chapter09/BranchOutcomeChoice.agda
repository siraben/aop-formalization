{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.BranchOutcomeChoice where

open import AoP.Common.Prelude
open import AoP.Chapter05.PowerRelator using (Lift; cover)
open import AoP.Chapter08.Thinning using (Min)
open import AoP.Common.NatOrder using (_≤_; rid)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)

-- One retained decomposition can return either 2 or 9. Selecting only
-- 9 satisfies both directions of relational power coverage. Its local
-- minimum is therefore 9, whereas the full image has minimum 2.
data Input : Set where one : Input
data Outcome : Nat → Input → Set where cheap : Outcome 2 one; dear : Outcome 9 one
Retained : Input → Set
Retained i = i ≡ one
Chosen Full : Nat → Set
Chosen n = n ≡ 9
Full n = Σ Input λ i → Retained i × Outcome n i
choice : Lift Outcome Chosen Retained
choice = cover (λ { _ refl → one , refl , dear }) (λ { .one refl → 9 , refl , dear })
selected-minimum : Min _≤_ 9 Chosen
selected-minimum = refl , λ { _ refl → rid 9 }
full-minimum : Min _≤_ 2 Full
full-minimum = (one , refl , cheap) , λ { _ (_ , refl , cheap) → rid 2 ; _ (_ , refl , dear) → s≤ (s≤ z≤) }
  where open AoP.Common.NatOrder using (s≤; z≤)
absent : Chosen 2 → ⊥
absent ()
