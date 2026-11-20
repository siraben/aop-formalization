{-# OPTIONS --safe --without-K #-}
module AoP.ConnectedFastDecision where

open import AoP.Prelude
open import AoP.ConnectedMaximum using (module Test)
open import AoP.ConnectedBlock using (module Law)
open import AoP.LongestConnectedBlock using (module Scan)
open import AoP.Subsequences using (there)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.ParagraphMinimum using (Dec)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 8.14. The streaming fold decides Cross by visiting members
-- of the active block. Replace that test by one comparison with its
-- greatest member; compare branch tags, not equality of proof terms.
module Fast {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
  (tr : ∀ {a b c} → Q a b → Q b c → Q a c)
  (fork : ∀ {a b c} → Q a c → Q b c → Q a b ⊎ Q b a)
  (test : ∀ a b → Dec (Q a b ⊎ Q b a)) where
  open Test Q rr tr fork
  open Scan Q rr test using (Cross; cross?)
  open Law Q using (Connected)
  cached? : ∀ a xs m → Greatest xs m → Dec (Cross a xs)
  cached? a xs m (at , upper) with test a m
  ... | inl (inl le) = inl (λ b p → fork le (upper b p))
  ... | inl (inr le) = inl (λ b p → inr (tr (upper b p) le))
  ... | inr no = inr λ cmp → no (cmp m at)
  tag : ∀ {P : Set} → Dec P → Bool
  tag (inl _) = true
  tag (inr _) = false
  agree : ∀ {P : Set} (u v : Dec P) → tag u ≡ tag v
  agree (inl _) (inl _) = refl
  agree (inr _) (inr _) = refl
  agree (inl yes) (inr no) with no yes
  ... | ()
  agree (inr no) (inl yes) with no yes
  ... | ()
  same-cut : ∀ a xs m (g : Greatest xs m) → tag (cached? a xs m g) ≡ tag (cross? a xs)
  same-cut a xs m g = agree (cached? a xs m g) (cross? a xs)
