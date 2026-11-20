{-# OPTIONS --safe --without-K #-}
module AoP.TeXPrefixShortest where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_)
open import AoP.TeXOccupiedPrefix using (module Print)
open import AoP.TeXFirstGrid using (Answer)
open import AoP.TeXClosestShortest using (scale; numerator)
open import AoP.TeXExternal using (length; Shortest; shortest)
open import AoP.TeXIntervalGrowth renaming (scale to grow) using ()
open import AoP.TeXRoundInterval using (module Decimal)
open import AoP.TeXFraction using (Digit; intern)
open import AoP.TeXGridStop using (InCell)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (comm; sym; unit; step; nil; dist)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

private
  times : ∀ a b c → (a * b) * c ≡ a * (b * c)
  times 0 b c = refl
  times (suc a) b c rewrite dist b (a * b) c | times a b c = refl
  bridge : ∀ a ds → grow (length ds) a ≡ a * scale ds
  bridge a [] = sym (step a 0 ∙ cong (a +_) (nil a) ∙ unit a)
  bridge a (d ∷ ds) = cong (_* 10) (bridge a ds) ∙ times a (scale ds) 10 ∙ cong (a *_) (comm (scale ds) 10)
  cast : ∀ {a b c e p} → a ≡ b → c ≡ e → InCell 131072 a c p → InCell 131072 b e p
  cast refl refl h = h
  subst : ∀ (P : Nat → Set) {a b} → a ≡ b → P a → P b
  subst P refl x = x

module Positive (t : Nat) (bound : 2 + suc (t * 2) ≤ 131072) where
  lo = suc (t * 2)
  hi = 2 + lo
  open Print lo bound
  n = Answer.places G.optimum
  w = R.Prefix.width prefix
  round-trip : intern digits ≡ suc t
  round-trip = Decimal.out t digits (cast {p = p} (cong (λ i → grow i lo) (sym w) ∙ bridge lo digits) (cong (λ i → grow i hi) (sym w) ∙ bridge hi digits) valid)
  minimal : ∀ es → intern es ≡ suc t → length digits ≤ length es
  minimal es ok = subst (_≤ length es) (sym w) (Answer.shortest G.optimum (length es) (numerator es) rival)
    where rival = cast {p = numerator es} (sym (bridge lo es)) (sym (bridge hi es)) (Decimal.into t es ok)
  certified : Shortest (suc t) digits
  certified = shortest round-trip minimal
