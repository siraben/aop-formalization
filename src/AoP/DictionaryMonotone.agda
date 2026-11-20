{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryMonotone where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Compression using (module Text)
open import AoP.UniformCodeCost using (module Law)
open import AoP.Naturality using (_++_)
open import AoP.NatOrder using (_≤_; rid; sum-mono; s≤)
open import Agda.Builtin.Nat using (Nat; _+_; suc)

-- Exercise 9.16. The empty branch compares with itself. In the snoc
-- branch the old costs are ordered, and new elements have equal charges
-- whenever both are literals or both are pointers, regardless of payload.
module Cost {A : Set} (c p : Nat) where
  open Text {A}
  open Law {A} using (bits)
  charge : Code → Nat
  charge (sym _) = c
  charge (ptr _ _) = p
  data Like : Code → Code → Set where
    literals′ : ∀ a b → Like (sym a) (sym b)
    pointers : ∀ i j k l → Like (ptr i j) (ptr k l)
  equal-charge : ∀ {u v} → Like u v → charge u ≡ charge v
  equal-charge (literals′ a b) = refl
  equal-charge (pointers i j k l) = refl

  private
    assoc+ : ∀ a b d → a + (b + d) ≡ (a + b) + d
    assoc+ 0 b d = refl
    assoc+ (suc a) b d = cong suc (assoc+ a b d)
    unit : ∀ a → a + 0 ≡ a
    unit 0 = refl
    unit (suc a) = cong suc (unit a)

  snoc-cost : ∀ xs u → bits c p (xs ++ (u ∷ [])) ≡ bits c p xs + charge u
  snoc-cost [] (sym a) = unit c
  snoc-cost [] (ptr i k) = unit p
  snoc-cost (sym a ∷ xs) u = cong (c +_) (snoc-cost xs u) ∙ assoc+ c (bits c p xs) (charge u)
  snoc-cost (ptr i k ∷ xs) u = cong (p +_) (snoc-cost xs u) ∙ assoc+ p (bits c p xs) (charge u)

  step : ∀ xs ys u v → bits c p xs ≤ bits c p ys → Like u v →
         bits c p (xs ++ (u ∷ [])) ≤ bits c p (ys ++ (v ∷ []))
  step xs ys u v le like rewrite snoc-cost xs u | snoc-cost ys v | equal-charge like = sum-mono le (rid _)
  base : bits c p [] ≤ bits c p []
  base = rid 0

-- Exercise 9.18. On equal prefixes the universal code-element relation
-- would compare a 2-bit pointer to a 1-bit literal in the wrong direction.
module Failure where
  open Text {Nat}
  open Law {Nat} using (bits)
  impossible : bits 1 2 (ptr 0 0 ∷ []) ≤ bits 1 2 (sym 0 ∷ []) → ⊥
  impossible (s≤ ())
