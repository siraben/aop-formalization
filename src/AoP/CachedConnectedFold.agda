{-# OPTIONS --safe --without-K #-}
module AoP.CachedConnectedFold where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Snoc using (Snoc; ε; _▻_; foldl)

-- 8.14, compact implementation. No block list is stored. A new
-- maximum preserves the minimum. When the maximum stays put, use
-- the common-upper-bound law to compare the newcomer to the minimum.
module Fold {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
  (tr : ∀ {a b c} → Q a b → Q b c → Q a c)
  (fork : ∀ {a b c} → Q a c → Q b c → Q a b ⊎ Q b a)
  (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  data State : Set where
    empty : State
    active : Snoc A → (lo hi : A) → Q lo hi → State
  step : State → A → State
  step empty a = active ε a a (rr a)
  step (active ds lo hi bounds) a with test a hi
  ... | inr _ = active (ds ▻ lo) a a (rr a)
  ... | inl (inr upper) = active ds lo a (tr bounds upper)
  ... | inl (inl lower) with fork lower bounds
  ...   | inl _ = active ds a hi lower
  ...   | inr _ = active ds lo hi bounds
  run = foldl empty step
  close : State → Snoc A
  close empty = ε
  close (active ds lo hi bounds) = ds ▻ lo
  thinlist : Snoc A → Snoc A
  thinlist t = close (run t)
