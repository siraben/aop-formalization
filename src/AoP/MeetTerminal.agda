{-# OPTIONS --safe --without-K #-}
module AoP.MeetTerminal where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Categories using (Category)
open import AoP.UniversalObjects using (module Universal)

-- Exercise 4.4. Fix two parallel relations. An object is a common
-- lower bound together with the two inclusions. A morphism includes
-- one bound in another. This is a thin category: parallel arrows are
-- equivalent without requiring Agda equality of inclusion proofs.
module Bounds {A B : Set} (R S : B ← A) where
  record Bound : Set₁ where
    constructor bound
    field carrier : B ← A
          left : carrier ⊆ R
          right : carrier ⊆ S
  open Bound

  bounds : Category _ _ _
  Category.Obj bounds = Bound
  Category.Hom bounds x y = carrier x ⊆ carrier y
  Category._≈_ bounds _ _ = ⊤
  Category.identity bounds x = x
  Category._∘_ bounds g f x = g (f x)
  Category.reflexive bounds = tt
  Category.symmetric bounds _ = tt
  Category.transitive bounds _ _ = tt
  Category.compose-cong bounds _ _ = tt
  Category.unitˡ bounds _ = tt
  Category.unitʳ bounds _ = tt
  Category.assoc bounds _ _ _ = tt

  meet : Bound
  meet = bound (R ⊓ S) fst snd

  open Universal bounds
  terminal : Terminal meet
  Terminal.enter terminal x p = left x p , right x p
  Terminal.unique terminal _ = tt
