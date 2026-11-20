{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SetSortUnique where

open import AoP.Common.Prelude
open import AoP.Chapter06.SetSort using (Same; same; Strict; nil; cons)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 6.25. Strict order makes the list representing a sorted
-- finite set unique. The two heads must be mutual lower bounds; once
-- they coincide, distinctness prevents a tail member from being matched
-- only by that head on the other side.
private
  antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
  antisym z≤ z≤ = refl
  antisym (s≤ p) (s≤ q) = cong suc (antisym p q)
  absurd : ∀ {A : Set} → ⊥ → A
  absurd ()
  head-bound : ∀ {a xs b} → Strict (a ∷ xs) → b ∈ (a ∷ xs) → a ≤ b
  head-bound s here = rid _
  head-bound (cons guard _) (there m) = fst (guard m)
  strip : ∀ {a : Nat} {xs ys} → Strict (a ∷ xs) → (∀ {b} → b ∈ (a ∷ xs) → b ∈ (a ∷ ys)) → ∀ {b} → b ∈ xs → b ∈ ys
  strip (cons guard _) f m with f (there m)
  ... | here = absurd (snd (guard m) refl)
  ... | there n = n

unique : ∀ {xs ys} → Strict xs → Strict ys → Same xs ys → xs ≡ ys
unique nil nil _ = refl
unique nil (cons _ _) law with Same.from law here
... | ()
unique (cons _ _) nil law with Same.to law here
... | ()
unique sx@(cons {a} _ tx) sy@(cons {b} _ ty) law with antisym (head-bound sx (Same.from law here)) (head-bound sy (Same.to law here))
... | refl = cong (a ∷_) (unique tx ty (same (strip sx (Same.to law)) (strip sy (Same.from law))))
