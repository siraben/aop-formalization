{-# OPTIONS --safe --without-K #-}
module AoP.HiddenTrace where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Subsequences using (_∈_)
open import AoP.QueryTrace using (module Tree)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 8.16. With decidable element equality the hidden comparison
-- can be inserted directly in the Boolean oracle. If the output on
-- equality includes v and the perturbed output excludes it, the
-- equality run queries the precise ordered pair (u,v).
module Law {A : Set} (dec : ∀ (x y : A) → (x ≡ y) ⊎ (x ≡ y → ⊥)) where
  module T = Tree {Q = A × A} {B = List A}
  equal : A × A → Bool
  equal (x , y) with dec x y
  ... | inl _ = true
  ... | inr _ = false

  module Pair (u v : A) where
    hidden : A × A → Bool
    hidden (x , y) with dec x u | dec y v
    ... | inl _ | inl _ = true
    ... | inr _ | _ = equal (x , y)
    ... | inl _ | inr _ = equal (x , y)

    locate : ∀ q → (equal q ≡ hidden q → ⊥) → q ≡ (u , v)
    locate (x , y) diff with dec x u | dec y v
    ... | inl refl | inl refl = refl
    ... | inr _ | _ with diff refl
    ...   | ()
    locate (x , y) diff | inl _ | inr _ with diff refl
    ...   | ()

    required : ∀ p → v ∈ T.eval equal p → (v ∈ T.eval hidden p → ⊥) → (u , v) ∈ T.trace equal p
    required p before after with T.Compare.distinguish equal hidden p changed
      where changed : T.eval equal p ≡ T.eval hidden p → ⊥
            changed eq = after (move eq before)
              where move : ∀ {xs ys} → xs ≡ ys → v ∈ xs → v ∈ ys
                    move refl x = x
    ... | q , m , diff with locate q diff
    ...   | refl = m
