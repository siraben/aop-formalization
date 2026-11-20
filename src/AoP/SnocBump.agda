{-# OPTIONS --safe --without-K #-}
module AoP.SnocBump where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_; foldl; fromSnoc)
open import AoP.Bump using (module Prune)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 8.12. Process the input from left to right. Compare each
-- new candidate with the last survivor, preserving the original order
-- when neither dominates. When both dominate, prefer the newcomer.
module Algorithm {A : Set} (Q : A → A → Set) (rr : ∀ x → Q x x)
                 (tr : ∀ {x y z} → Q x y → Q y z → Q x z) where
  open Prune Q rr tr using (Comparison; first; second; retain)
  module Run (cmp : ∀ x y → Comparison x y) where
    bump : Snoc A → A → Snoc A
    bump ε x = ε ▻ x
    bump (ys ▻ y) x with cmp x y
    ... | first _ = ys ▻ x
    ... | second _ = ys ▻ y
    ... | retain = (ys ▻ y) ▻ x

    thinlist = foldl ε bump

-- All candidates have the same score. Each traversal favors its
-- newcomer, so one keeps the leftmost value and the other the rightmost.
module Example where
  Q : Bool → Bool → Set
  Q _ _ = ⊤
  module P = Prune Q (λ _ → tt) (λ _ _ → tt)
  cmp : ∀ a b → P.Comparison a b
  cmp _ _ = P.first tt
  module Left = Algorithm.Run Q (λ _ → tt) (λ _ _ → tt) cmp
  module Right = P.Algorithm cmp
  snoc-result : fromSnoc (Left.thinlist ((ε ▻ false) ▻ true)) ≡ true ∷ []
  snoc-result = refl
  cons-result : Right.thinlist (false ∷ true ∷ []) ≡ false ∷ []
  cons-result = refl
