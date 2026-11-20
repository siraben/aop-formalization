{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.BracketSpineDecision where

open import AoP.Common.Prelude
open import AoP.Chapter09.BracketSpineDominance using (module Law)
open import AoP.Chapter09.Bracketing using (module Model)
open import AoP.Chapter08.ParagraphMinimum using (Dec; le?)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter01.Trees using (Tree; tip; bin)
open import AoP.Common.NatOrder using (rid; chain)
open import AoP.Chapter09.PoolPruning using (module Sweep)
open import Agda.Builtin.Nat using (Nat)

module Check {A S : Set} (atom : A → S) (combine : S → S → S) (charge : S → S → Nat)
             (eq? : ∀ (x y : S) → Dec (x ≡ y)) where
  open Law atom combine charge
  open Model atom combine charge using (size; cost)
  self : ∀ t → Spine t t
  self (tip _) = leaf refl
  self (bin l r) = fork (self l) (refl , rid _)
  compose : ∀ {t u v} → Spine t u → Spine u v → Spine t v
  compose (leaf p) (leaf q) = leaf (p ∙ q)
  compose (fork l (p , a)) (fork l′ (q , b)) = fork (compose l l′) ((p ∙ q) , chain a b)
  closed? : ∀ t u → Dec (Closed t u)
  closed? t u with eq? (size t) (size u) | le? (cost t) (cost u)
  ... | inr no | _ = inr (λ p → no (fst p))
  ... | inl _ | inr no = inr (λ p → no (snd p))
  ... | inl p | inl q = inl (p , q)
  spine? : ∀ t u → Dec (Spine t u)
  spine? (tip x) (tip y) with eq? (atom x) (atom y)
  ... | inl p = inl (leaf p)
  ... | inr no = inr λ { (leaf p) → no p }
  spine? (tip _) (bin _ _) = inr λ ()
  spine? (bin _ _) (tip _) = inr λ ()
  spine? (bin l r) (bin l′ r′) with spine? l l′ | closed? r r′
  ... | inr no | _ = inr λ { (fork p _) → no p }
  ... | inl _ | inr no = inr λ { (fork _ q) → no q }
  ... | inl p | inl q = inl (fork p q)
  module Thin where
    open Sweep Spine self spine? using (prune)
    thinlist : List (Tree A) → List (Tree A)
    thinlist ts = fst (prune ts)
    correct = λ ts → snd (prune ts)
