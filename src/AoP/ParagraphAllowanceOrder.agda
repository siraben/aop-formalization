{-# OPTIONS --safe --without-K #-}
module AoP.ParagraphAllowanceOrder where

open import AoP.Prelude
open import AoP.ParagraphSnocStep using (State; _≼_; fewer; narrower)
open import AoP.NatOrder using (_≤_; z≤; s≤; sum-mono; rid; chain; weaken)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (assoc; unit; swap)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- One extra closed line costs margin+1 units in the allowance.
-- A legal open line occupies at most margin units, so even the widest
-- greedy last line cannot consume that advantage over a rival.
module Law (margin : Nat) where
  total : State → Nat
  total (k , w) = k * suc margin + w
  private
    grow : ∀ {a b} → a ≤ b → a * suc margin ≤ b * suc margin
    grow z≤ = z≤
    grow (s≤ p) = sum-mono (rid _) (grow p)
    pad : ∀ a b → a ≤ a + b
    pad 0 b = z≤
    pad (suc a) b = s≤ (pad a b)
    move : ∀ a b → a + b ≡ b + a
    move a b = Arithmetic.sym (cong (a +_) (unit b)) ∙ swap a b 0 ∙ cong (b +_) (unit a)
  monotone : ∀ {s t} → snd s ≤ margin → s ≼ t → total s ≤ total t
  monotone fits (narrower p) = sum-mono (rid _) p
  monotone fits (fewer {k} {j} {l} {h} lt) rewrite move (k * suc margin) l =
    chain (sum-mono (weaken fits) (rid (k * suc margin))) (chain (grow lt) (pad (j * suc margin) h))

  -- For histories of the same input, the flat text width f is common
  -- to both balance equations. Cancel it to obtain the waste order.
  private
    cancel : ∀ f {a b} → f + a ≤ f + b → a ≤ b
    cancel 0 p = p
    cancel (suc f) (s≤ p) = cancel f p
  waste-order : ∀ f a b s t → a + f ≡ total s → b + f ≡ total t → snd s ≤ margin → s ≼ t → a ≤ b
  waste-order f a b s t e d fits adv = cancel f (cast (move f a ∙ e) (move f b ∙ d) (monotone fits adv))
    where cast : ∀ {a b x y : Nat} → a ≡ x → b ≡ y → x ≤ y → a ≤ b
          cast refl refl p = p
