{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.TourVariantExamples where

open import AoP.Common.Prelude
open import AoP.Chapter08.TourVariants using (Mode; both; neither; extra; module Solve)
open import Agda.Builtin.Nat using (Nat)

-- Exercises 8.27–8.28. With one interior city there are three
-- possible assignments in each variant. Choose costs so that the
-- newly permitted assignment is strictly better than either old one.
data City : Set where start middle end : City

-- Passing through middle costs two on each leg. A direct leg costs
-- nine, so visiting middle only once costs eleven instead of four.
via : City → City → Nat
via start end = 9
via end start = 9
via _ _ = 1
module Shared = Solve via end both

shared-result : fst (Shared.solve (middle ∷ []) start start) ≡ Shared.step extra Shared.close
shared-result = refl
shared-cost : Shared.cost start start (Shared.step {middle} extra Shared.close) ≡ 4
shared-cost = refl

-- Reverse the preference: now a direct leg costs one and any leg
-- through middle costs eighteen. Skipping middle costs two in total.
direct : City → City → Nat
direct start end = 1
direct end start = 1
direct _ _ = 9
module Skip = Solve direct end neither

skip-result : fst (Skip.solve (middle ∷ []) start start) ≡ Skip.step extra Skip.close
skip-result = refl
skip-cost : Skip.cost start start (Skip.step {middle} extra Skip.close) ≡ 2
skip-cost = refl
