{-# OPTIONS --safe --without-K #-}
module AoP.LowerBoundCalculations where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Power using (ℙ; Λ)
open import AoP.Thinning using (Min)

-- §7.1 (7.1–4). A lower bound makes a comparison with every member,
-- whether or not it is a member itself. Test the definition on the
-- three kinds of sets used in the minimum calculations.
module Law {A : Set} (R : A ← A) where
  Lower : A → ℙ A → Set
  Lower a X = ∀ x → X x → R a x
  single : A → ℙ A
  single b x = x ≡ b
  at-single : ∀ {a b} → Lower a (single b) → R a b
  at-single bound = bound _ refl
  on-single : ∀ {a b} → R a b → Lower a (single b)
  on-single edge _ refl = edge

  -- A transposed relation is its fibre. Division asks for precisely
  -- the same comparisons, one for each output of the given input.
  at-fibre : ∀ {B} (S : A ← B) {a b} → Lower a (Λ S b) → (R ／ (S ˘)) a b
  at-fibre S bound {x} edge = bound x edge
  on-fibre : ∀ {B} (S : A ← B) {a b} → (R ／ (S ˘)) a b → Lower a (Λ S b)
  on-fibre S bound x edge = bound edge

  -- A union witness names its originating set. Retaining the index
  -- gives a family of bounds; unpacking it gives a bound for the union.
  module Union {I : Set} (family : I → ℙ A) where
    union : ℙ A
    union x = Σ I (λ i → family i x)
    distribute : ∀ {a} → Lower a union → ∀ i → Lower a (family i)
    distribute bound i x member = bound x (i , member)
    combine : ∀ {a} → (∀ i → Lower a (family i)) → Lower a union
    combine bounds x (i , member) = bounds i x member

  -- A singleton minimum must first be its sole member. Its only
  -- remaining comparison is reflexivity at that particular value.
  minimum-test : ∀ {a b} → Min R a (single b) → (a ≡ b) × R a b
  minimum-test (same , bound) = same , at-single bound
  minimum-build : ∀ {a b} → (a ≡ b) × R a b → Min R a (single b)
  minimum-build (same , edge) = same , on-single edge
  reflexive : (∀ b → Min R b (single b)) → ∀ b → R b b
  reflexive all b = snd (minimum-test (all b))
  singleton-min : (∀ b → R b b) → ∀ b → Min R b (single b)
  singleton-min rr b = minimum-build (refl , rr b)
