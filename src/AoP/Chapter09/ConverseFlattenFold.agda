{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.ConverseFlattenFold where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip)
open import AoP.Chapter09.BracketSpine using (options; leaves)
open import AoP.Chapter09.BracketEnumeration using (enumerate; sound; complete)
open import AoP.Chapter02.Folds using (⦅_∣_⦆)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (concat)
open import AoP.Chapter05.Subsequences using (_∈_)

-- Exercise 9.14. Make the empty suffix explicit in the fold carrier.
-- Prepending to it produces one tip; prepending to a nonempty suffix
-- inserts a new leaf at each permissible position on the left spine.
module Build {A : Set} where
  data State : Set where
    start : State
    pool : List (Tree A) → State
  step : A → State → State
  step a start = pool (tip a ∷ [])
  step a (pool ts) = pool (concat (map (options a) ts))
  fold = ⦅ start ∣ step ⦆
  nonempty : ∀ a xs → fold (a ∷ xs) ≡ pool (enumerate (a ∷ xs))
  nonempty a [] = refl
  nonempty a (b ∷ xs) = cong (step a) (nonempty b xs)
  unpack : State → List (Tree A)
  unpack start = []
  unpack (pool ts) = ts
  agrees : ∀ xs → unpack (fold xs) ≡ enumerate xs
  agrees [] = refl
  agrees (a ∷ xs) = cong unpack (nonempty a xs)
  forward : ∀ xs t → t ∈ unpack (fold xs) → leaves t ≡ xs
  forward xs t rewrite agrees xs = sound xs
  backward : ∀ xs t → leaves t ≡ xs → t ∈ unpack (fold xs)
  backward xs t rewrite agrees xs = complete xs t
