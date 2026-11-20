{-# OPTIONS --safe --without-K #-}
module AoP.VanSchedule where

open import AoP.Prelude
open import AoP.Reserves
open import AoP.SecureBlock using (module Check)
open import AoP.Paragraph using (Nonempty; _∷⁺_)
open import AoP.LineBreaks using (module Breaks)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.FiniteMinimum using (module Search)
open import AoP.Polynomial using (inl; inr)
open import AoP.Complement using (⊥)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat; suc)

-- §7.5. A visit lets the bank reset its reserves between adjacent blocks.
-- For a nonempty transaction stream, minimize these internal boundaries;
-- counting the initial delivery as a visit would add one to every cost.
-- Reuse the partition generator from paragraph layout: its break patterns
-- do not depend on word lengths or margins. Security replaces line width
-- as the feasibility predicate. This solver enumerates rather than prunes.
module Schedule (capacity : Nat) where
  open Bank capacity
  open Check capacity using (secure?)
  open Breaks (λ (_ : Tx) → 0) 0
  Block = Nonempty Tx
  Plan = Nonempty Block

  feasible : Block → List Block → Set
  feasible (t ∷⁺ ts) [] = Secure (t ∷ ts)
  feasible (t ∷⁺ ts) (b ∷ bs) = Secure (t ∷ ts) × feasible b bs

  decide : ∀ b bs → Dec (feasible b bs)
  decide (t ∷⁺ ts) [] = secure? (t ∷ ts)
  decide (t ∷⁺ ts) (b ∷ bs) with secure? (t ∷ ts) | decide b bs
  ... | inr no | _ = inr (λ p → no (fst p))
  ... | inl _ | inr no = inr (λ p → no (snd p))
  ... | inl a | inl b = inl (a , b)

  Valid : Plan → Set
  Valid (b ∷⁺ bs) = feasible b bs
  visits : Plan → Nat
  visits (b ∷⁺ bs) = count bs
    where
    count : List Block → Nat
    count [] = 0
    count (_ ∷ bs) = suc (count bs)

  module S = Search Valid (λ { (b ∷⁺ bs) → decide b bs }) visits
  data Answer (t : Tx) (ts : List Tx) : Set where
    impossible : (∀ p → Partition t ts p → Valid p → ⊥) → Answer t ts
    optimal : ∀ p → Partition t ts p → Valid p →
              (∀ q → Partition t ts q → Valid q → visits p ≤ visits q) → Answer t ts

  solve : ∀ t ts → Answer t ts
  solve t ts with S.scan (enumerate t ts)
  ... | S.none no = impossible (λ p part → no p (complete part))
  ... | S.best p m ok least = optimal p (sound t ts m) ok (λ q part → least q (complete part))
