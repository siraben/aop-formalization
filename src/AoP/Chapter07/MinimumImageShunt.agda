{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MinimumImageShunt where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (graph)
open import AoP.Chapter04.Power using (ℙ; ℰ)
open import AoP.Chapter08.Thinning using (Min)

-- §7.1 (7.7). To bound the whole image it suffices to compare with
-- every successor of every input member. Recover an image witness by
-- pairing the input membership proof with the edge that produced it.
module Image {A B : Set} (R : B ← B) (S : B ← A) (X : ℙ A) where
  Bounds : B → Set
  Bounds b = ∀ a → X a → ∀ c → S c a → R b c
  expand : ∀ b → Min R b (ℰ S X) → ℰ S X b × Bounds b
  expand b (member , wins) = member , (λ a x c edge → wins c (a , edge , x))
  collect : ∀ b → ℰ S X b × Bounds b → Min R b (ℰ S X)
  collect b (member , wins) = member , (λ { c (a , edge , x) → wins a x c edge })

-- (7.8). A function contributes exactly one successor per rival.
-- Keep the preimage witnessing feasibility, compare it with rivals
-- under the pulled-back relation, then return its function value.
module Function {A B : Set} (R : B ← B) (f : A → B) (X : ℙ A) where
  module I = Image R (graph f) X
  Pull : A ← A
  Pull a c = R (f a) (f c)
  shunt : ∀ b → Min R b (ℰ (graph f) X) → ℰ (graph f) (λ a → Min Pull a X) b
  shunt b m with I.expand b m
  ... | (a , refl , x) , wins = a , refl , x , (λ c rival → wins c rival (f c) refl)
  restore : ∀ b → ℰ (graph f) (λ a → Min Pull a X) b → Min R b (ℰ (graph f) X)
  restore .(f a) (a , refl , x , wins) = I.collect (f a) ((a , refl , x) , (λ { c rival .(f c) refl → wins c rival }))
