{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DPContextExample where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _∘_; _˘; _⊓_)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 9.2 with the identity lifting. An input has one child
-- decomposition, and its sole feasible outcome is its own bit. Flip
-- reverses the ordinary bit order, but the two different bits never
-- occur as rival outcomes at the same input.
data _≤_ : Bool ← Bool where
  same : ∀ {b} → b ≤ b
  rise : false ≤ true
flip : Bool → Bool
flip false = true
flip true = false
H T : Bool ← Bool
H = _≡_
T a b = a ≡ flip b
context-monotone : ∀ {x y} → (_≤_ ⊓ (H ∘ H ˘)) x y → flip x ≤ flip y
context-monotone (_ , _ , refl , refl) = same
no-global-monotonicity : (∀ {x y} → x ≤ y → flip x ≤ flip y) → ⊥
no-global-monotonicity m with m rise
... | ()
-- Even with the universal thinning comparison, two decompositions of
-- the same parent must agree. Replaying the rival therefore suffices.
injective : ∀ {x y} → flip x ≡ flip y → x ≡ y
injective {false} {false} _ = refl
injective {true} {true} _ = refl
context-match : ∀ {b c v} → (T ˘ ∘ T) c b → H v b → Σ Bool λ w → H w c × (flip w ≤ flip v)
context-match (_ , refl , eq) refl with injective eq
... | refl = _ , refl , same
no-global-match : (∀ b c → Σ Bool λ w → H w c × (flip w ≤ flip b)) → ⊥
no-global-match m with m true false
... | .false , refl , ()
