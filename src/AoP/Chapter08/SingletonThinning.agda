{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.SingletonThinning where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter08.Thinning using (Thin; thin; Min; Pred)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 8.5. Returning just a is a valid thinning exactly when a
-- belongs to the input and dominates every input member. This gives
-- thin-elimination without requiring reflexivity or transitivity.
module Law {A : Set} (R : A ← A) (X : Pred A) (a : A) where
  Only : Pred A
  Only b = b ≡ a

  eliminate : Min R a X → Thin R Only X
  eliminate (member , best) = thin (λ { refl → member }) (λ b x → a , refl , best b x)

  minimum : Thin R Only X → Min R a X
  minimum t = Thin.subset t refl , best
    where best : ∀ b → X b → R a b
          best b x with Thin.cover t b x
          ... | .a , refl , edge = edge

-- With equality, both Booleans can be kept but neither singleton
-- covers the other Boolean. Thus eliminating thin may lose inputs.
both : Bool → Set
both _ = ⊤
keep-both : Thin _≡_ both both
keep-both = thin (λ x → x) λ b m → b , m , refl
no-minimum : ∀ b → Min _≡_ b both → ⊥
no-minimum false (_ , best) with best true tt
... | ()
no-minimum true (_ , best) with best false tt
... | ()
