{-# OPTIONS --safe --without-K #-}
module AoP.LeftMinimumBlock where

open import AoP.Prelude
open import AoP.Relations using (cons; nil)
open import AoP.Subsequences using (_∈_; here; there; Subseq)
open import AoP.ConnectedBlock using (module Law)
open import AoP.NatOrder using (_≤_; z≤)
open import Agda.Builtin.Nat using (Nat)
open import AoP.Complement using (⊥)

-- Exercise 8.15. A nonempty block is admissible when its first
-- element dominates every later one. Shortening its tail keeps the
-- same first element, so even arbitrary tail deletions preserve it.
module Block {A : Set} (Q : A → A → Set) where
  LeftMin : A → List A → Set
  LeftMin a xs = ∀ b → b ∈ xs → Q a b

  restrict : ∀ {a xs ys} → Subseq xs ys → LeftMin a ys → LeftMin a xs
  restrict sub bound b xb = bound b (Law.member Q sub xb)

  -- With a current left minimum b, checking a new first element a
  -- against b alone suffices. Necessity comes from b's membership.
  necessary : ∀ {a b xs} → LeftMin a (b ∷ xs) → Q a b
  necessary p = p _ here
  prepend : (∀ {a b c} → Q a b → Q b c → Q a c) →
            ∀ {a b xs} → Q a b → LeftMin b xs → LeftMin a (b ∷ xs)
  prepend tr ab p _ here = ab
  prepend tr ab p c (there m) = tr ab (p c m)

-- Deleting the first element can invalidate the block, unlike 8.14:
-- [0,2,1] has left minimum 0, but [2,1] has no left minimum at 2.
module Example where
  open Block {Nat} _≤_
  valid : LeftMin 0 (2 ∷ 1 ∷ [])
  valid _ _ = z≤
  invalid : LeftMin 2 (1 ∷ []) → ⊥
  invalid p with p 1 here
  ... | AoP.NatOrder.s≤ ()
