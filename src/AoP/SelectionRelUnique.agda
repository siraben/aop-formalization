{-# OPTIONS --safe --without-K #-}
module AoP.SelectionRelUnique where

open import AoP.Prelude
open import AoP.Selection
open import AoP.SelectionSort using (length; loop; remaining; shorter)
open import AoP.SelectionEquation using (sort)
open import AoP.NatOrder using (_≤_; s≤; rid)
open import Agda.Builtin.Nat using (Nat; suc)

-- §6.6. Even a relation satisfying the unfold equation can have
-- neither extra nor missing outputs. The backward direction constructs
-- the graph witness; the forward direction rules out all other lists.
module Law (R : List Nat → List Nat → Set)
  (nil-in : R [] []) (nil-out : ∀ {ys} → R [] ys → ys ≡ [])
  (put : ∀ x xs {ys} → let c = select x xs in R (Choice.rest c) ys → R (x ∷ xs) (Choice.minimum c ∷ ys))
  (get : ∀ x xs {ys} → let c = select x xs in R (x ∷ xs) ys → Σ (List Nat) λ zs → (ys ≡ (Choice.minimum c ∷ zs)) × R (Choice.rest c) zs) where
  intro : ∀ n xs (p : length xs ≤ n) → R xs (fst (loop n xs p))
  intro n [] p = nil-in
  intro (suc n) (x ∷ xs) (s≤ p) with select x xs | put x xs
  ... | chose k rs rem lb | build = build (intro n rs (remaining (shorter rem) p))

  elim : ∀ n xs (p : length xs ≤ n) {ys} → R xs ys → ys ≡ fst (loop n xs p)
  elim n [] p r = nil-out r
  elim (suc n) (x ∷ xs) (s≤ p) r with select x xs | get x xs r
  ... | chose k rs rem lb | zs , eq , sub = eq ∙ cong (k ∷_) (elim n rs (remaining (shorter rem) p) sub)

  graph-in : ∀ xs → R xs (sort xs)
  graph-in xs = intro (length xs) xs (rid _)
  graph-out : ∀ xs ys → R xs ys → ys ≡ sort xs
  graph-out xs ys = elim (length xs) xs (rid _)
