{-# OPTIONS --safe --without-K #-}
module AoP.SnocBumpProof where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.Bump using (module Prune)
open import AoP.SnocBump using (module Algorithm)
open import AoP.Subsequences using (Subseq)

-- Read both snoc lists from their last element backwards. The snoc
-- bump is then precisely the cons bump, including its tie policy.
-- Coverage is insensitive to direction, and the subsequence witness
-- matches survivors to distinct source positions in this common order.
back : ∀ {A} → Snoc A → List A
back ε = []
back (xs ▻ x) = x ∷ back xs

module Proof {A : Set} (Q : A → A → Set) (rr : ∀ x → Q x x)
             (tr : ∀ {x y z} → Q x y → Q y z → Q x z) where
  module P = Prune Q rr tr
  module Run (cmp : ∀ x y → P.Comparison x y) where
    module C = P.Algorithm cmp
    module S = Algorithm.Run Q rr tr cmp
    step : ∀ xs x → back (S.bump xs x) ≡ C.bump x (back xs)
    step ε x = refl
    step (ys ▻ y) x with cmp x y
    ... | P.first _ = refl
    ... | P.second _ = refl
    ... | P.retain = refl

    fusion : ∀ xs → back (S.thinlist xs) ≡ C.thinlist (back xs)
    fusion ε = refl
    fusion (xs ▻ x) = step (S.thinlist xs) x ∙ cong (C.bump x) (fusion xs)

    coverage : ∀ xs → C.Covers (back (S.thinlist xs)) (back xs)
    coverage xs rewrite fusion xs = C.correct (back xs)

    ordered : ∀ xs → Subseq (back (S.thinlist xs)) (back xs)
    ordered xs rewrite fusion xs = C.ordered (back xs)
