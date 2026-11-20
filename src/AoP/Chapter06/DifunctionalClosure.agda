{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.DifunctionalClosure where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Complement using (_⊔_)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter04.ModularRefinement using (zigzag)

-- Exercise 6.8. Start with R. Whenever three existing edges form a
-- forward-backward-forward path, add the missing edge of its rectangle.
-- A finite derivation records each such addition. Induction shows that
-- every difunctional extension must contain every edge we generate.
module Close {A B : Set} (R : B ← A) where
  step : (B ← A) → B ← A
  step X = R ⊔ (X ∘ X ˘ ∘ X)

  data Closed : B ← A where
    seed : ∀ {b a} → R b a → Closed b a
    rectangle : ∀ {b a c d} → Closed b c → Closed d c → Closed d a → Closed b a

  roll : step Closed ⊆ Closed
  roll (inl r) = seed r
  roll (inr (_ , p , _ , q , r)) = rectangle p q r
  unroll : Closed ⊆ step Closed
  unroll (seed r) = inl r
  unroll (rectangle p q r) = inr (_ , p , _ , q , r)

  least : (X : B ← A) → step X ⊆ X → Closed ⊆ X
  least X pre (seed r) = pre (inl r)
  least X pre (rectangle p q r) = pre (inr (_ , least X pre p , _ , least X pre q , least X pre r))

  contract : Closed ∘ Closed ˘ ∘ Closed ⊆ Closed
  contract (_ , p , _ , q , r) = rectangle p q r
  expand : Closed ⊆ Closed ∘ Closed ˘ ∘ Closed
  expand = zigzag Closed

  smallest : (X : B ← A) → R ⊆ X → X ∘ X ˘ ∘ X ⊆ X → Closed ⊆ X
  smallest X contains contracts = least X λ { (inl r) → contains r ; (inr path) → contracts path }
