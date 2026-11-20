{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.IndirectMeet where

open import AoP.Common.Prelude

-- Exercise 4.1. In a hom-poset compare the two bracketings indirectly:
-- they admit exactly the same lower bounds. Both tests reduce by the
-- meet universal property to three component inequalities. Testing at
-- each candidate itself gives the desired mutual inclusion.
module Laws {P : Set} (_≤_ : P → P → Set) (id : ∀ x → x ≤ x)
            (_∧_ : P → P → P)
            (split : ∀ {x a b} → x ≤ (a ∧ b) → (x ≤ a) × (x ≤ b))
            (pair : ∀ {x a b} → x ≤ a → x ≤ b → x ≤ (a ∧ b)) where
  module At (a b c : P) where
    L = (a ∧ b) ∧ c
    R = a ∧ (b ∧ c)

    right : ∀ x → x ≤ L → x ≤ R
    right x p with split p
    ... | ab , xc with split ab
    ...   | xa , xb = pair xa (pair xb xc)

    left : ∀ x → x ≤ R → x ≤ L
    left x p with split p
    ... | xa , bc with split bc
    ...   | xb , xc = pair (pair xa xb) xc

    associative : (L ≤ R) × (R ≤ L)
    associative = right L (id L) , left R (id R)
