{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.RelatorEmptyMembership where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)
open import AoP.Chapter06.MembershipDivisionLaw using (module Law)

-- Exercise 6.21 for abstract liftings on concrete Rel. Factor the empty
-- column A ← ⊤ through ⊥. With no members, every member of v lies in
-- that composite vacuously. The expansion law then supplies a value of
-- F ⊥ as the intermediate point, contradicting the emptiness hypothesis.
module Proof (F : Set → Set) (L : ∀ {A B} → B ← A → F B ← F A)
  (join : ∀ {A B C} (R : C ← B) (S : B ← A) → L R ∘ L S ⊆ L (R ∘ S))
  (split : ∀ {A B C} (R : C ← B) (S : B ← A) → L (R ∘ S) ⊆ L R ∘ L S)
  (member : ∀ A → A ← F A) where
  open Law F L join split member
  Entire = ∀ (A : Set) (v : F A) → Σ A (λ a → member A a v)
  forward : Entire → F ⊥ → ⊥
  forward all v = fst (all ⊥ v)
  backward : IdentityLaw → (∀ P → ((P → ⊥) → ⊥) → P) → (F ⊥ → ⊥) → Entire
  backward law dne empty A v = dne _ λ none → empty (fst (CompositeLaw.expand (generalize law) R S {b = v} {a = tt} (vacant none)))
    where R : A ← ⊥
          R a ()
          S : ⊥ ← ⊤
          S () x
          vacant : (Σ A (λ a → member A a v) → ⊥) → Columns (R ∘ S) v tt
          vacant none {x} m with none (x , m)
          ... | ()
