{-# OPTIONS --safe --without-K #-}
module AoP.PowerMiddleBounds where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Power using (ℙ; ℰ; _≐_)
open import AoP.PowerRelator using (Lift; module Composition)

-- §5.4. For the hard inclusion in the composition proof we can use
-- the largest possible intermediate set. 'Middle b' requires both
-- an incoming edge from X and an outgoing edge into Z. Using just
-- one image could admit a dead end on the other side.
module Path {A B C : Set} (S : C ← B) (R : B ← A) (Z : ℙ C) (X : ℙ A) where
  open Composition S R Z X
  images : Middle ≐ (λ b → ℰ (S ˘) Z b × ℰ R X b)
  fst images b ((c , z , s) , (a , x , r)) = (c , s , z) , (a , r , x)
  snd images b ((c , s , z) , (a , r , x)) = (c , z , s) , (a , x , r)

  largest : ∀ (Y : ℙ B) → Lift S Z Y → Lift R Y X → ∀ b → Y b → Middle b
  largest Y second first b y = Lift.forward second b y , Lift.backward first b y

  -- A rival factorization covers the endpoints, so every necessary
  -- endpoint witness survives enlargement to Middle. No selection of
  -- one preferred path (or decidable membership) is required.
  enlarge : ∀ (Y : ℙ B) → Lift S Z Y → Lift R Y X → Lift S Z Middle × Lift R Middle X
  enlarge Y second first = factor (compose Y second first)
