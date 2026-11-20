{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.AccessibleMeet where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter06.Inductive using (Acc; acc)
open import AoP.Chapter04.Complement using (_⊔_; ⊥)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 6.15. Restricting permitted recursive calls preserves
-- accessibility. For a meet, either factor supplies the induction.
restrict : ∀ {A} {R S : A ← A} → R ⊆ S → ∀ {a} → Acc S a → Acc R a
restrict incl (acc down) = acc λ b p → restrict incl (down b (incl p))

meet : ∀ {A} {R S : A ← A} → (∀ a → Acc R a) → ∀ a → Acc (R ⊓ S) a
meet wf a = restrict fst (wf a)

-- Each relation permits one directed step on two vertices. Their
-- union permits alternating forever. Every vertex has a predecessor,
-- so an alleged accessibility derivation refutes itself by descent.
data Up : Bool ← Bool where up : Up false true
data Down : Bool ← Bool where down : Down true false

up-wf : ∀ a → Acc Up a
up-wf false = acc λ _ ()
up-wf true = acc λ { _ up → up-wf false }

down-wf : ∀ a → Acc Down a
down-wf true = acc λ _ ()
down-wf false = acc λ { _ down → down-wf true }

cycle : ∀ a → Acc (Up ⊔ Down) a → ⊥
cycle false (acc smaller) = cycle true (smaller true (inr down))
cycle true (acc smaller) = cycle false (smaller false (inl up))
