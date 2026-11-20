{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.LiberalPrecondition where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Power using (ℙ; Λ; _≐_)
private variable A B C : Set

-- Exercise 4.52. An input meets the weakest liberal precondition if
-- every possible output meets the requested postcondition. An input
-- with no outputs qualifies vacuously. This is the power transpose of
-- left division by membership, written pointwise across universes.
wlp : (B ← A) → ℙ B → ℙ A
wlp R post a = ∀ {b} → R b a → post b

stages : (R : C ← B) (S : B ← A) (post : ℙ C) →
         wlp (R ∘ S) post ≐ wlp S (wlp R post)
stages R S post = (λ a all s r → all (_ , r , s)) ,
                  (λ { a all (b , r , s) → all s r })

-- More possible outputs impose more obligations. For the converse,
-- test with the exact set of S-outputs at the input in question.
module Order (R S : B ← A) where
  Below = (post : ℙ B) (a : A) → wlp S post a → wlp R post a
  reverse : R ⊆ S → Below
  reverse sub post a all r = all (sub r)
  reflect : Below → R ⊆ S
  reflect test {b} {a} r = test (Λ S a) a (λ s → s) r
