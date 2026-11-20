{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.PartyChoiceOrder where

open import AoP.Common.Prelude
open import AoP.Chapter05.ListMeet using (Align; nil; cons)
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_)

-- Exercise 7.43. Each subordinate supplies two candidate guest lists:
-- one including their root and one excluding it. If both candidates
-- improve, any previous choice can be matched on the same side.
-- R better worse records comparison by total conviviality.
module Law {A : Set} (R : A ← A) where
  Pair : Set
  Pair = A × A
  Better : Pair ← Pair
  Better u v = R (fst u) (fst v) × R (snd u) (snd v)
  data Choose : A ← Pair where
    left : ∀ x y → Choose x (x , y)
    right : ∀ x y → Choose y (x , y)

  match : ∀ {p q x} → Better q p → Choose x p → Σ A λ y → Choose y q × R y x
  match {q = a , b} (r , s) (left x y) = a , left a b , r
  match {q = a , b} (r , s) (right x y) = b , right a b , s

  -- In the book's composition the old output is the target, so use
  -- the converse comparison (old ← improved) in both positions.
  Choose-mono : Choose ∘ (λ p q → Better q p) ⊆ (λ x y → R y x) ∘ Choose
  Choose-mono (p , chosen , improves) with match improves chosen
  ... | y , pick , bound = y , bound , pick

  -- Map choose independently across the forest. The matched choices
  -- stay aligned with the same direct reports, including on ties.
  forest : ∀ {ps qs xs} → Align Better qs ps → Align Choose xs ps →
           Σ (List A) λ ys → Align Choose ys qs × Align R ys xs
  forest nil nil = [] , nil , nil
  forest (cons better bs) (cons pick ps) with match better pick | forest bs ps
  ... | y , choice , bound | ys , choices , bounds = (y ∷ ys) , cons choice choices , cons bound bounds
