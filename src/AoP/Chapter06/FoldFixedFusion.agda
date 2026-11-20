{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.FoldFixedFusion where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)

-- Exercise 6.6. Both fixed-point tests use the same candidate S ∘ r.
-- Expose the constructor layer of the source with out. Composition of
-- lifted relations is the only relator equation used in this calculation.
module Law (F : Set → Set) (lift : ∀ {A B} → B ← A → F B ← F A)
  (split : ∀ {A B C} (P : C ← B) (Q : B ← A) → lift (P ∘ Q) ⊆ lift P ∘ lift Q)
  (join : ∀ {A B C} (P : C ← B) (Q : B ← A) → lift P ∘ lift Q ⊆ lift (P ∘ Q))
  {D A B : Set} (out : D → F D) (R : A ← F A) (T : B ← F B) (S : B ← A) where
  Step : ∀ {V} → V ← F V → V ← D → V ← D
  Step alg X b d = (alg ∘ lift X) b (out d)

  module Folds (r : A ← D) (t : B ← D)
    (roll : Step R r ⊆ r) (unroll : r ⊆ Step R r)
    (least : ∀ X → Step T X ⊆ X → t ⊆ X)
    (greatest : ∀ X → X ⊆ Step T X → X ⊆ t) where

    -- (6.4): split F(S ∘ r), apply the algebra inequality to the
    -- outer two edges, then roll the remaining R layer back into r.
    prefix : T ∘ lift S ⊆ S ∘ R → Step T (S ∘ r) ⊆ S ∘ r
    prefix law (v , alg , fsr) with split S r fsr
    ... | u , fs , fr with law (v , alg , fs)
    ...   | b , s , layer = b , s , roll (u , layer , fr)
    first : T ∘ lift S ⊆ S ∘ R → t ⊆ S ∘ r
    first law = least (S ∘ r) (prefix law)

    -- (6.5): unfold r, apply the opposite algebra inequality, and
    -- join the two lifted edges. The candidate is now a postfixpoint.
    postfix : S ∘ R ⊆ T ∘ lift S → S ∘ r ⊆ Step T (S ∘ r)
    postfix law (b , s , p) with unroll p
    ... | u , layer , fr with law (b , s , layer)
    ...   | v , alg , fs = v , alg , join S r (u , fs , fr)
    second : S ∘ R ⊆ T ∘ lift S → S ∘ r ⊆ t
    second law = greatest (S ∘ r) (postfix law)
