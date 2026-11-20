{-# OPTIONS --safe --without-K #-}
module AoP.LocalWinnerFold where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)
open import AoP.MonotoneConstructor using (module Container)

-- Exercise 7.37 for containers. A deterministic node operation chooses
-- a minimum among the available results for its given child answers.
-- Compare against a competing run in two steps: improve its children
-- by induction, then improve its choice at this node by local optimality.
module Law (Shape : Set) (Pos : Shape → Set) {A : Set} (R : A ← A)
           (tr : ∀ {a b c} → R a b → R b c → R a c)
           (choices : (s : Shape) → (Pos s → A) → A → Set)
           (f : (s : Shape) → (Pos s → A) → A)
           (best : ∀ s xs → Min R (f s xs) (choices s xs))
           (mono : ∀ s xs ys → (∀ i → R (xs i) (ys i)) → R (f s xs) (f s ys)) where
  open Container Shape Pos
  solve : Tree → A
  solve (node s ts) = f s (λ i → solve (ts i))

  data Run : A ← Tree where
    build : ∀ {s ts xs a} → (∀ i → Run (xs i) (ts i)) → choices s xs a → Run a (node s ts)

  feasible : ∀ t → Run (solve t) t
  feasible (node s ts) = build (λ i → feasible (ts i)) (fst (best s _))

  bound : ∀ {t a} → Run a t → R (solve t) a
  bound (build {s} {ts} {xs} children choice) = tr
    (mono s (λ i → solve (ts i)) xs (λ i → bound (children i)))
    (snd (best s xs) _ choice)

  optimal : ∀ t → Min R (solve t) (λ a → Run a t)
  optimal t = feasible t , λ _ run → bound run
