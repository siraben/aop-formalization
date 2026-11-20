{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.ScriptLengthOrder where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (graph)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_; s≤)

-- Exercise 9.6. Prepending one command to each edit script adds one
-- to both lengths. The commands need not agree: the head comparison
-- is universal. This justifies comparing tails before extending them.
module Law {Command : Set} where
  Script = List Command
  R : Script ← Script
  R xs ys = len xs ≤ len ys
  Layer : (Command × Script) ← (Command × Script)
  Layer p q = ⊤ × R (snd p) (snd q)
  extend : Command × Script → Script
  extend (c , xs) = c ∷ xs

  monotone : graph extend ∘ Layer ⊆ R ∘ graph extend
  monotone ((c , xs) , refl , _ , shorter) = _ , s≤ shorter , refl
