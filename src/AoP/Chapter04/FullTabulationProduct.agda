{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.FullTabulationProduct where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_∘_; _˘; _⊆_)
open import AoP.Chapter04.Shunting using (graph)
open import AoP.Chapter04.RelUnitObject using (Full)
open import AoP.Chapter04.TabulationMediator using (module Table)
open import AoP.Chapter04.TabulationMeet using (module Match)
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.SpanProduct using (module Over)

-- §4.3. A table for the full relation has one row for every possible
-- pair of column values. Because the relation imposes no restriction,
-- *every* span factors through the table. This is exactly the product
-- property in Fun, with the two column functions as projections.
module Product {A B T : Set} (left : T → A) (right : T → B)
  (find : Full ⊆ graph left ∘ graph right ˘)
  (joint : ∀ x y → left x ≡ left y → right x ≡ right y → x ≡ y) where
  module S = Over Fun A B
  columns = S.span T left right
  module Factor = Table Full left right find (λ _ → tt) joint
  terminal : S.U.Terminal columns
  S.U.Terminal.enter terminal (S.span X h k) = S.via (M.row chosen) (M.target chosen) (M.source chosen)
    where module V = Factor.Span h k
          module M = V.Mediator
          chosen = V.factor (λ _ → tt)
  S.U.Terminal.unique terminal {S.span X h k} (S.via m h-law k-law) = V.unique rival (V.factor (λ _ → tt))
    where module V = Factor.Span h k
          rival : V.Mediator
          V.Mediator.row rival = m
          V.Mediator.target rival = h-law
          V.Mediator.source rival = k-law

-- For the ordinary pair type, the lookup operation is just pairing.
-- The last equation of §4.3 now reads: a pair is the output exactly
-- when its two projections pass the two separate column tests.
module Pairs {A B D : Set} (h : D → A) (k : D → B) where
  find : Full ⊆ graph (fst {B = λ _ → B}) ∘ graph (snd {A = A}) ˘
  find {b = a} {a = b} _ = (a , b) , refl , refl
  joint : ∀ (p q : A × B) → fst p ≡ fst q → snd p ≡ snd q → p ≡ q
  joint (a , b) (.a , .b) refl refl = refl
  module M = Match fst snd h k joint
  module W = M.Included Full find (λ _ → tt) (λ _ → tt)
  columns : graph (λ d → h d , k d) ⊆ M.M
  columns = W.graph-in
  paired : M.M ⊆ graph (λ d → h d , k d)
  paired = W.graph-out
