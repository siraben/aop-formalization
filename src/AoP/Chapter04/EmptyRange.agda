{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.EmptyRange where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.RangeRotation using (ran)
open import AoP.Chapter04.Complement using (⊥)
private variable A B C : Set

-- Exercise 4.31. A relation has no edges precisely when there is no
-- output in its range. An edge supplies its own range witness; a range
-- witness already contains an edge. Emptiness therefore lets us forget
-- the input when comparing two descriptions of a triangle.
Empty : (B ← A) → Set
Empty R = ∀ {b a} → R b a → ⊥

project : (R : B ← A) → Empty R → Empty (ran R)
project R absent (_ , _ , edge) = absent edge
restore : (R : B ← A) → Empty (ran R) → Empty R
restore R absent {b} {a} edge = absent (refl , a , edge)

module Triangle (R : C ← B) (S : B ← A) (T : C ← A) where
  L = (R ∘ S) ⊓ T
  K = R ⊓ (T ∘ S ˘)

  rotate : ran L ⊆ ran K
  rotate (eq , a , (b , r , s) , t) = eq , b , r , a , t , s
  unrotate : ran K ⊆ ran L
  unrotate (eq , b , r , a , t , s) = eq , a , (b , r , s) , t

  forward : Empty L → Empty K
  forward noL = restore K (λ k → project L noL (unrotate k))
  backward : Empty K → Empty L
  backward noK = restore L (λ l → project K noK (rotate l))
