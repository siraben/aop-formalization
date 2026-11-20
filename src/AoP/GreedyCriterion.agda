{-# OPTIONS --safe --without-K #-}
module AoP.GreedyCriterion where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)
open import AoP.MonotoneConstructor using (module Container)

-- Exercise 7.36, deterministic container fold. Test a node only on
-- reachable subproblems whose chosen child answers are already optimal.
-- Competitors may use ANY feasible child answers for those same trees.
module Law (S : Set) (P : S → Set) {A : Set} (R : A ← A)
  (options : (s : S) → (P s → A) → A → Set)
  (pick : (s : S) → (P s → A) → A)
  (allowed : ∀ s xs → options s xs (pick s xs)) where
  open Container S P
  solve : Tree → A
  solve (node s ts) = pick s (λ i → solve (ts i))
  data Run : A ← Tree where
    build : ∀ {s ts xs y} → (∀ i → Run (xs i) (ts i)) → options s xs y → Run y (node s ts)
  feasible : ∀ t → Run (solve t) t
  feasible (node s ts) = build (λ i → feasible (ts i)) (allowed s _)

  Winner : Tree → Set
  Winner t = Min R (solve t) (λ y → Run y t)
  Local = ∀ (s : S) (ts : P s → Tree) → (∀ i → Winner (ts i)) → ∀ xs y → (∀ i → Run (xs i) (ts i)) →
          options s xs y → R (pick s (λ i → solve (ts i))) y

  necessary : (∀ t → Winner t) → Local
  necessary all s ts _ xs y runs opt = snd (all (node s ts)) y (build runs opt)
  sufficient : Local → ∀ t → Winner t
  sufficient test (node s ts) = feasible (node s ts) , λ where
    y (build {xs = xs} runs opt) → test s ts (λ i → sufficient test (ts i)) xs y runs opt
