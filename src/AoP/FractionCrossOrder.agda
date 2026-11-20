{-# OPTIONS --safe --without-K #-}
module AoP.FractionCrossOrder where

open import AoP.Prelude
open import AoP.RationalFloorOrder using (Fraction; _⊆_; Cut)
open import AoP.NatOrder using (_≤_; rid; chain; z≤; s≤; sum-mono)
open import AoP.FractionThreshold using (strip)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open Fraction

module Arithmetic where
  sym : ∀ {x y : Nat} → x ≡ y → y ≡ x
  sym refl = refl
  unit : ∀ a → a + 0 ≡ a
  unit 0 = refl
  unit (suc a) = cong suc (unit a)
  move : ∀ a b → a + suc b ≡ suc (a + b)
  move 0 b = refl
  move (suc a) b = cong suc (move a b)
  swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
  swap 0 b c = refl
  swap (suc a) b c = cong suc (swap a b c) ∙ sym (move b (a + c))
  step : ∀ a b → a * suc b ≡ a + a * b
  step 0 b = refl
  step (suc a) b = cong suc (cong (b +_) (step a b) ∙ swap b a (a * b))
  nil : ∀ a → a * 0 ≡ 0
  nil 0 = refl
  nil (suc a) = nil a
  comm : ∀ a b → a * b ≡ b * a
  comm 0 b = sym (nil b)
  comm (suc a) b = cong (b +_) (comm a b) ∙ sym (step b a)
  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc 0 b c = refl
  assoc (suc a) b c = cong suc (assoc a b c)
  dist : ∀ a b c → (a + b) * c ≡ a * c + b * c
  dist 0 b c = refl
  dist (suc a) b c = cong (c +_) (dist a b c) ∙ sym (assoc c (a * c) (b * c))
  switch : ∀ a b c → (a * b) * c ≡ (a * c) * b
  switch 0 b c = refl
  switch (suc a) b c rewrite dist b (a * b) c | dist c (a * c) b | comm b c | switch a b c = refl
  scale : ∀ k {a b} → a ≤ b → a * k ≤ b * k
  scale k z≤ = z≤
  scale k (s≤ p) = sum-mono (rid k) (scale k p)
  cast : ∀ {a b c d} → a ≡ c → b ≡ d → a ≤ b → c ≤ d
  cast refl refl p = p

open Arithmetic

Cross : Fraction → Fraction → Set
Cross f g = r f * suc (d g) ≤ r g * suc (d f)
-- Test inclusion at f itself. Conversely, multiply the probe and
-- fraction comparisons by positive denominators and cancel f's.
necessary : ∀ f g → f ⊆ g → Cross f g
necessary f g incl = incl (r f) (d f) (rid _)
sufficient : ∀ f g → Cross f g → f ⊆ g
sufficient f g le m s probe = strip l h df 0 (s≤ z≤) (cast refl (sym (unit (h * df))) together)
  where df = suc (d f); dg = suc (d g); ds = suc s
        l = m * dg; h = r g * ds
        together : l * df ≤ h * df
        together = chain (cast (switch m df dg) (switch (r f) ds dg) (scale dg probe))
                         (cast refl (switch (r g) df ds) (scale ds le))
