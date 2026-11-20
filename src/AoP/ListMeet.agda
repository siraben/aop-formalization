{-# OPTIONS --safe --without-K #-}
module AoP.ListMeet where

open import AoP.Prelude
open import AoP.Relations

-- Exercise 5.18, the list instance. An edge aligns the two lists by
-- position. Two alignments of the same lists necessarily use the same
-- constructors, so their element witnesses can be paired positionwise.
data Align {A B : Set} (R : B ← A) : List B ← List A where
  nil : Align R [] []
  cons : ∀ {b a bs as} → R b a → Align R bs as → Align R (b ∷ bs) (a ∷ as)

module Law {A B : Set} (R S : B ← A) where
  split : Align (R ⊓ S) ⊆ Align R ⊓ Align S
  split nil = nil , nil
  split (cons (r , s) rs) with split rs
  ... | l , h = cons r l , cons s h

  join : Align R ⊓ Align S ⊆ Align (R ⊓ S)
  join (nil , nil) = nil
  join (cons r l , cons s h) = cons (r , s) (join (l , h))
