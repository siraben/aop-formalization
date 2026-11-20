{-# OPTIONS --safe --without-K #-}
module AoP.LeftmostMinimumFold where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Complement using (⊥)
open import AoP.Thinning using (Min)

-- §7.1. A connected comparison may admit distinct tied values. Test
-- the head against the tail winner, choosing the head on *any* yes.
-- A mere choice of one of the two order directions could break ties
-- differently; the negative branch below certifies a genuine refusal.
module Fold {A : Set} (R : A → A → Set) (rr : ∀ a → R a a)
  (trans : ∀ {a b c} → R a b → R b c → R a c)
  (conn : ∀ a b → R a b ⊎ R b a) (test : ∀ a b → R a b ⊎ (R a b → ⊥)) where
  data First (w : A) : List A → Set where
    head : ∀ {xs} → First w (w ∷ xs)
    pass : ∀ {a xs} → (R a w → ⊥) → First w xs → First w (a ∷ xs)

  record Winner (xs : List A) : Set where
    constructor win
    field value : A
          minimum : Min R value (_∈ xs)
          first : First value xs
  scan : ∀ a xs → Winner (a ∷ xs)
  scan a [] = win a (here , (λ { _ here → rr a ; _ (there ()) })) head
  scan a (b ∷ xs) with scan b xs
  ... | win w (member , least) pos with test a w
  ...   | inl beats = win a (here , (λ { _ here → rr a ; y (there m) → trans beats (least y m) })) head
  ...   | inr loses with conn a w
  ...     | inl impossible with loses impossible
  ...       | ()
  scan a (b ∷ xs) | win w (member , least) pos | inr loses | inr better =
    win w (there member , (λ { _ here → better ; y (there m) → least y m })) (pass loses pos)
