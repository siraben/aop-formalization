{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXLoopWidth where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; s≤; z≤; rid; sum-mono; chain; weaken)
open import AoP.Chapter10.TeXResidualLoop
open import AoP.Chapter10.TeXPrinterStep using (module Emit)
open import AoP.Chapter10.TeXResidualRival using (drop)
open import AoP.Chapter10.TeXGridStop using (InCell)
open import AoP.Chapter10.OpenUpperDigit using (Upper)
open import AoP.Chapter03.TeXFraction using (Digit)
open import AoP.Chapter10.TeXClosestShortest using (scale)
open import AoP.Chapter10.TeXExternal using (length)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; sym; unit; nil; step)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _-_)

private
  times : ∀ a b c → (a * b) * c ≡ a * (b * c)
  times 0 b c = refl
  times (suc a) b c rewrite dist b (a * b) c | times a b c = refl
  one : ∀ a → a * 1 ≡ a
  one a = step a 0 ∙ cong (a +_) (nil a) ∙ unit a
  clash : ∀ {x} {X : Set} → suc x ≤ x → X
  clash {0} ()
  clash {suc x} (s≤ h) = clash h
  pad : ∀ x y → x ≤ x + y
  pad 0 y = z≤
  pad (suc x) y = s≤ (pad x y)
  positive : ∀ ds → 1 ≤ scale ds
  positive [] = rid 1
  positive (d ∷ ds) = chain (positive ds) (pad (scale ds) _)
  project : ∀ w p q d v t → 1 ≤ v → Upper w (q * 10) d → InCell w (p * (10 * v)) (q * (10 * v)) t → InCell w ((p * 10 - d * w) * v) ((q * 10 - d * w) * v) (t - d * v)
  project w p q d (suc v) t pos u h rewrite sym (times p 10 (suc v)) | sym (times q 10 (suc v)) = drop w (p * 10) (q * 10) d v t u h

Short : List Digit → Result → Set
Short es exhausted = 0 ≡ 0
Short es (printed ds) = length ds ≤ length es

module Proof (k : Nat) where
  w = suc k
  minimal : ∀ fuel p j (b : suc j ≤ w) es t → InCell w (p * scale es) (suc j * scale es) t → Short es (Loop.run k fuel p j b)
  minimal fuel 0 j b es t h = z≤
  minimal 0 (suc p) j b es t h = refl
  minimal (suc f) (suc p) j b [] 0 (lo , hi) rewrite one (suc p) with lo
  ... | ()
  minimal (suc f) (suc p) j b [] (suc t) (lo , hi) rewrite one (suc j) = clash (chain (s≤ (pad w (t * w))) (chain hi b))
  minimal (suc f) (suc p) j b (e ∷ es) t h = lift r (minimal f E.low (pred E.high) nb es (t - E.d * scale es) rival)
    where module E = Emit k j 0 (suc p) b
          nb = next-bound k E.high E.next-high
          r = Loop.run k f E.low (pred E.high) nb
          rival = transport (nonzero E.high (fst E.next-high)) (project w (suc p) (suc j) E.d (scale es) t (positive es) E.local h)
            where transport : ∀ {a c} → a ≡ c → InCell w (E.low * scale es) (a * scale es) (t - E.d * scale es) → InCell w (E.low * scale es) (c * scale es) (t - E.d * scale es)
                  transport refl h = h
          lift : ∀ s → Short es s → Short (e ∷ es) (prepend E.letter s)
          lift exhausted h = refl
          lift (printed ds) h = s≤ h
