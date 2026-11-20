{-# OPTIONS --safe --without-K #-}
module AoP.BalanceConvention where

open import AoP.Prelude
open import AoP.BalanceFold
open import AoP.Steep using (_and_)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 3.5 leaves the size assigned to null relevant to the
-- answer. With size zero every bottom node fails: its left subtree
-- occupies 0/1. A failed child forces every ancestor to fail too.
private
  reject : ∀ b → (b and false) ≡ false
  reject true = refl
  reject false = refl

module Test {A : Set} where
  module Z = Check {A} 0
  module U = Check {A} 1
  no-node : ∀ l (a : A) r → Z.balanced (node l a r) ≡ false
  no-node null a null = refl
  no-node null a (node l b r) = refl
  no-node (node l b r) a t rewrite no-node l b r = reject _

  -- With size one at null, a bottom node has fraction 1/3 and size
  -- three. As a left child it contributes 3/5 (accepted); as a right
  -- child it leaves a left fraction of 1/5 (rejected).
  leaf : A → Tree A
  leaf a = node null a null
  bottom : ∀ a → U.scan (leaf a) ≡ (3 , true)
  bottom a = refl
  heavier-left : ∀ a b → U.scan (node (leaf a) b null) ≡ (5 , true)
  heavier-left a b = refl
  heavier-right : ∀ a b → U.scan (node null b (leaf a)) ≡ (5 , false)
  heavier-right a b = refl
