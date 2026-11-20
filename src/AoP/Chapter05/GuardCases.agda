{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.GuardCases where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter04.Shunting using (Map)
open import AoP.Chapter05.CopairCancellation using (copair)

-- Exercise 5.17. Represent a Boolean test by a decidable predicate on
-- the input. Its two diagonal relations retain the value and record
-- passing or failing. The converse copair tags the value accordingly.
module Cases {A : Set} (P : A → Set) (dec : ∀ a → P a ⊎ (P a → ⊥)) where
  yes no : A ← A
  yes b a = (b ≡ a) × P a
  no b a = (b ≡ a) × (P a → ⊥)
  guard = copair yes no ˘

  function : Map guard
  Map.entire function {a} refl with dec a
  ... | inl p = inl a , (refl , p) , refl , p
  ... | inr n = inr a , (refl , n) , refl , n
  Map.simple function {inl _} {inl _} (_ , (refl , _) , refl , _) = refl
  Map.simple function {inr _} {inr _} (_ , (refl , _) , refl , _) = refl
  Map.simple function {inl _} {inr _} (_ , (refl , p) , refl , n) with n p
  ... | ()
  Map.simple function {inr _} {inl _} (_ , (refl , n) , refl , p) with n p
  ... | ()

  module Branches {B : Set} (R S T : B ← A) where
    conditional = copair S T ∘ guard
    Obligations = (R ∘ yes ⊆ S) × (R ∘ no ⊆ T)
    split : R ⊆ conditional → Obligations
    split incl = left , right
      where
      left : R ∘ yes ⊆ S
      left (_ , r , refl , p) with incl r
      ... | inl _ , s , refl , _ = s
      ... | inr _ , _ , refl , n with n p
      ...   | ()
      right : R ∘ no ⊆ T
      right (_ , r , refl , n) with incl r
      ... | inr _ , t , refl , _ = t
      ... | inl _ , _ , refl , p with n p
      ...   | ()
    join : Obligations → R ⊆ conditional
    join (l , h) {a = a} r with dec a
    ... | inl p = inl a , l (a , r , refl , p) , refl , p
    ... | inr n = inr a , h (a , r , refl , n) , refl , n
