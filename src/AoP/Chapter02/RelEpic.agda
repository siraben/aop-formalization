{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.RelEpic where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 2.7. Onto means each output is hit. Epic means observing
-- composites distinguishes any two relations following this one.
Eq : ∀ {A B : Set} → (B ← A) → (B ← A) → Set
Eq R S = (R ⊆ S) × (S ⊆ R)
Epic : ∀ {A B : Set} → (B ← A) → Set₁
Epic {B = B} R = ∀ {C : Set} (S T : C ← B) → Eq (S ∘ R) (T ∘ R) → Eq S T

-- A single input hits both Booleans. Testing for false and testing for
-- true then give indistinguishable composites, despite differing tests.
cover : Bool ← ⊤
cover _ _ = ⊤
onto : ∀ b → Σ ⊤ (cover b)
onto b = tt , tt

at : Bool → ⊤ ← Bool
at key _ b = b ≡ key

not-epic : Epic cover → ⊥
not-epic epic with fst (epic (at false) (at true) ((λ _ → true , refl , tt) , (λ _ → false , refl , tt))) {tt} {false} refl
... | ()

-- Conversely give each output its own private input plus one shared
-- input. The private inputs let us recover all observations, hence
-- cancel the relation. The shared input prevents single-valuedness.
data Input : Set where
  private-key : Bool → Input
  shared : Input

fan : Bool ← Input
fan b (private-key k) = b ≡ k
fan b shared = ⊤

recover : ∀ {C : Set} {S T : C ← Bool} → (S ∘ fan) ⊆ (T ∘ fan) → S ⊆ T
recover incl {a = b} sb with incl {a = private-key b} (b , sb , refl)
... | _ , tb , refl = tb

fan-epic : Epic fan
fan-epic S T (f , g) = recover {S = S} {T} f , recover {S = T} {S} g

not-single : (∀ {x b c} → fan b x → fan c x → b ≡ c) → ⊥
not-single unique with unique {shared} {false} {true} tt tt
... | ()
