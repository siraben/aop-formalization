{-# OPTIONS --safe --without-K #-}
module AoP.RangeJoins where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Joins using (⋃)
open import AoP.RangeRotation using (ran)

-- Exercise 4.29. An output of a union has an input and a branch that
-- reaches it. Choose the branch first: the same input then shows that
-- this output belongs to that branch's range. The diagonal equality
-- is retained, so this is equality of range *relations*.
module Family {A B I : Set} (R : I → B ← A) where
  distribute : ran (⋃ R) ⊆ ⋃ (λ i → ran (R i))
  distribute (eq , a , i , r) = i , eq , a , r

  collect : ⋃ (λ i → ran (R i)) ⊆ ran (⋃ R)
  collect (i , eq , a , r) = eq , a , i , r
