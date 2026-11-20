{-# OPTIONS --safe --without-K #-}
module AoP.TeXPrinterAgreement where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; rid; chain; weaken)
open import AoP.TeXFixedWidthUnique using (recover)
open import AoP.TeXWidthAgreement using (width)
open import AoP.TeXDistanceScale using (power) renaming (width to scale-width)
open import AoP.TeXClosestShortest using (scale; numerator)
open import AoP.TeXExternal using (Shortest; length)
open import AoP.TeXFraction using (Digit)
open import AoP.OpenUpperDigit using (Upper; only)
open import AoP.TeXGridMinimum using (module Positive)
open import AoP.TeXOccupiedPrefix using (module Print)
open import AoP.TeXPrefixShortest as Two using (module Calibration)
import AoP.TeXSinglePrinter as Single
import AoP.TeXBoundedPrinter as Double
import AoP.TeXLoopRoundTrip as Trip
import AoP.TeXLoopGreatest as Best
open import AoP.TeXResidualLoop using (Result; printed)
open import AoP.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

private
  same : ∀ w h a b → Upper w h a → Upper w h b → a ≡ b
  same w 0 a b (() , _) _
  same w (suc h) a b = only w h a b
  cast : ∀ w a {h g} → h ≡ g → Upper w h a → Upper w g a
  cast w a refl p = p

module At (t : Nat) (bound : suc (suc (suc (t * 2))) ≤ 131072) where
  module T = Trip.Positive t bound
  module P = Print T.lo bound
  hi = suc T.j
  proof : ∀ ds → T.result ≡ printed ds → Shortest (suc t) ds → ds ≡ P.digits
  proof ds eq opt = recover ds P.digits len (same 131072 (hi * scale ds) (numerator ds) P.p a b)
    where len = width opt (Two.Positive.certified t bound)
          a = extract T.result eq (Best.Proof.best 131071 5 T.lo T.j bound)
            where extract : ∀ r → r ≡ printed ds → Best.Proof.Good 131071 hi r → Upper 131072 (hi * scale ds) (numerator ds)
                  extract .(printed ds) refl h = h
          end = cong P.G.H (Arithmetic.sym (P.R.Prefix.width P.prefix)) ∙ Calibration.bridge hi P.digits ∙ cong (hi *_) (scale-width P.digits ∙ cong power (Arithmetic.sym len) ∙ Arithmetic.sym (scale-width ds))
          b = cast 131072 P.p end (P.R.Prefix.greatest P.prefix)

agree : ∀ n (b : suc n ≤ 65536) → fst (Single.extern n b) ≡ fst (Double.extern n b)
agree 0 b = refl
agree (suc t) b = At.proof t bound (fst sol) (fst (snd sol)) (snd (snd sol))
  where bound : suc (suc (suc (t * 2))) ≤ 131072
        bound = chain (weaken (rid _)) (Arithmetic.scale 2 {a = suc (suc t)} {b = 65536} b)
        sol = Single.Certified.solve t bound
