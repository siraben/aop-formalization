{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ParagraphMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph
open import AoP.Chapter08.LineBreaks
open import AoP.Common.FiniteMinimum
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §8.5. The least-waste layout is only meaningful if every line fits.
-- Enumerate all break patterns, reject over-wide lines, and minimize
-- among survivors. If a word alone exceeds the margin, failure is a
-- meaningful answer: the negative branch certifies infeasibility.
-- This reference solver is exponential, not the book's thinning algorithm.
Dec : Set → Set
Dec P = P ⊎ (P → ⊥)

le? : ∀ n m → Dec (n ≤ m)
le? zero m = inl z≤
le? (suc n) zero = inr (λ ())
le? (suc n) (suc m) with le? n m
... | inl p = inl (s≤ p)
... | inr no = inr λ { (s≤ p) → no p }

module Solve {W : Set} (len : W → Nat) (margin : Nat) (charge : Nat → Nat) where
  open Layout len margin
  open Breaks len margin
  fits? : ∀ l ls → Dec (fitFrom l ls)
  fits? l [] = le? (width l) margin
  fits? l (k ∷ ks) with le? (width l) margin | fits? k ks
  ... | inr no | _ = inr (λ p → no (fst p))
  ... | inl _ | inr no = inr (λ p → no (snd p))
  ... | inl a | inl b = inl (a , b)

  module S = Search Fits (λ { (l ∷⁺ ls) → fits? l ls }) (waste charge)

  data Answer (w : W) (ws : List W) : Set where
    impossible : (∀ p → Partition w ws p → Fits p → ⊥) → Answer w ws
    optimum : (p : Para) → Partition w ws p → Fits p →
              (∀ q → Partition w ws q → Fits q → waste charge p ≤ waste charge q) → Answer w ws

  solve : ∀ w ws → Answer w ws
  solve w ws with S.scan (enumerate w ws)
  ... | S.none no = impossible (λ p part → no p (complete part))
  ... | S.best p mem ok bound = optimum p (sound w ws mem) ok (λ q part → bound q (complete part))
