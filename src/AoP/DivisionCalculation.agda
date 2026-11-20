{-# OPTIONS --safe --without-K #-}
module AoP.DivisionCalculation where

open import AoP.Prelude
open import AoP.Relations
open import AoP.LeftDivision using (_＼_)
open import AoP.Complement using (_⊔_)
open import AoP.Polynomial using (inl; inr)
private variable A B C D : Set

-- §4.4, intermediate division laws. An edge of a composite includes
-- a middle point and two edges. Dividing by the composite consumes
-- both at once; successive divisions consume them one at a time.
module Composite (R : D ← C) (S : C ← B) (T : D ← A) where
  stages : (R ∘ S) ＼ T ⊆ S ＼ (R ＼ T)
  stages h s r = h (_ , r , s)
  together : S ＼ (R ＼ T) ⊆ (R ∘ S) ＼ T
  together h (_ , r , s) = h s r

-- A union on the left introduces two cases for the input. A meet
-- on the right asks for two outputs from the same input witness.
module Union (R S : C ← B) (T : C ← A) where
  apart : (R ⊔ S) ＼ T ⊆ (R ＼ T) ⊓ (S ＼ T)
  apart h = (λ r → h (inl r)) , (λ s → h (inr s))
  merge : (R ＼ T) ⊓ (S ＼ T) ⊆ (R ⊔ S) ＼ T
  merge (h , k) (inl r) = h r
  merge (h , k) (inr s) = k s

module Meet (R : C ← B) (S T : C ← A) where
  apart : R ＼ (S ⊓ T) ⊆ (R ＼ S) ⊓ (R ＼ T)
  apart h = (λ r → fst (h r)) , (λ r → snd (h r))
  merge : (R ＼ S) ⊓ (R ＼ T) ⊆ R ＼ (S ⊓ T)
  merge (h , k) r = h r , k r
