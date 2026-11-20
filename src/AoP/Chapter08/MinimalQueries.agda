{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.MinimalQueries where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter05.Subsequences using (_∈_)
open import AoP.Chapter07.MinimalComparison using (Test)
open import AoP.Chapter08.Thinning using (Min)
open import AoP.Chapter08.HiddenComparison using (module Hidden)
open import AoP.Chapter08.HiddenTrace using (module Law)
open import Agda.Builtin.Bool using (Bool; true)

-- Exercise 8.16. Specify correctness only for oracles representing
-- preorders. On one fixed input, every correct decision tree must
-- query every distinct ordered pair of members on its equality run.
module Solver {A : Set} (dec : ∀ (x y : A) → (x ≡ y) ⊎ (x ≡ y → ⊥)) (xs : List A) where
  open Law dec
  X = λ a → a ∈ xs
  Represents : (A × A → Bool) → (A → A → Set) → Set
  Represents f R = ∀ a b → ((f (a , b) ≡ true) → R a b) × (R a b → f (a , b) ≡ true)

  private
    absurd : ∀ {P : Set} → ⊥ → P
    absurd ()

  equal-ok : Represents equal _≡_
  equal-ok a b with dec a b
  ... | inl eq = (λ _ → eq) , (λ _ → refl)
  ... | inr no = (λ ()) , λ eq → absurd (no eq)

  Correct : T.Program → Set₁
  Correct p = ∀ f R → Represents f R → (∀ a → R a a) →
    (∀ {a b c} → R a b → R b c → R a c) → ∀ a →
    ((a ∈ T.eval f p) → Min (Test R) a X) × (Min (Test R) a X → a ∈ T.eval f p)

  module Adversary (u v : A) (different : u ≡ v → ⊥) where
    open Hidden u v different
    open Pair u v
    hidden-ok : Represents hidden Edge
    hidden-ok a b with dec a u | dec b v
    ... | inl au | inl bv = (λ _ → inr (au , bv)) , (λ _ → refl)
    ... | inr no | _ = (λ t → inl (fst (equal-ok a b) t)) , λ where
      (inl eq) → snd (equal-ok a b) eq
      (inr (au , _)) → absurd (no au)
    ... | inl au | inr no = (λ t → inl (fst (equal-ok a b) t)) , λ where
      (inl eq) → snd (equal-ok a b) eq
      (inr (_ , bv)) → absurd (no bv)

    must-query : ∀ p → Correct p → X u → X v → (u , v) ∈ T.trace equal p
    must-query p ok xu xv = required p (snd (ok equal _≡_ equal-ok (λ _ → refl) _∙_ v) (before X xv))
      (λ kept → after X xu (fst (ok hidden Edge hidden-ok (λ _ → inl refl) trans v) kept))
