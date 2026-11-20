{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXLoopGreatest where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; s≤; z≤)
open import AoP.Chapter10.TeXResidualLoop
open import AoP.Chapter10.TeXPrinterStep using (module Emit)
open import AoP.Chapter10.TeXClosestShortest using (scale; numerator)
open import AoP.Chapter10.OpenUpperDigit using (Upper)
open import AoP.Chapter10.TeXGridDigit using (translate)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; switch; sym; step; nil; unit)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- The strict digit rule chooses the greatest numerator below the open
-- endpoint at the width it ultimately prints. Restore the leading digit
-- as a translation by d*v whole grid steps (v is the suffix scale).
private
  times : ∀ a b c → (a * b) * c ≡ a * (b * c)
  times 0 b c = refl
  times (suc a) b c rewrite dist b (a * b) c | times a b c = refl
  one : ∀ a → a * 1 ≡ a
  one a = step a 0 ∙ cong (a +_) (nil a) ∙ unit a
  join : ∀ w q d r v x → d * w + r ≡ q * 10 → Upper w (r * v) x → Upper w (q * (10 * v)) (d * v + x)
  join w q d r v x eq h = cast (cong (_+ (r * v)) (switch d v w) ∙ sym (dist (d * w) r v) ∙ cong (_* v) eq ∙ times q 10 v) (translate w (d * v) (r * v) x h)
    where cast : ∀ {a b} → a ≡ b → Upper w a (d * v + x) → Upper w b (d * v + x)
          cast refl h = h
module Proof (k : Nat) where
  w = suc k
  Good : Nat → Result → Set
  Good q exhausted = 0 ≡ 0
  Good q (printed ds) = Upper w (q * scale ds) (numerator ds)
  best : ∀ fuel p j (b : suc j ≤ w) → Good (suc j) (Loop.run k fuel p j b)
  best fuel 0 j b rewrite one (suc j) | unit w = s≤ z≤ , b
  best 0 (suc p) j b = refl
  best (suc f) (suc p) j b = lift r (best f E.low (pred E.high) nb)
    where module E = Emit k j 0 (suc p) b
          nb = next-bound k E.high E.next-high
          r = Loop.run k f E.low (pred E.high) nb
          lift : ∀ s → Good (suc (pred E.high)) s → Good (suc j) (prepend E.letter s)
          lift exhausted h = refl
          lift (printed ds) h = join w (suc j) E.d E.high (scale ds) (numerator ds) E.exact (transport (nonzero E.high (fst E.next-high)) h)
            where transport : ∀ {a c} → a ≡ c → Good c (printed ds) → Good a (printed ds)
                  transport refl h = h
