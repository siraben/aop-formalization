{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.AdjacentThin where

open import AoP.Common.Prelude
open import AoP.Chapter08.Bump using (module Prune)

-- Exercise 8.13. Compare adjacent candidates before recursing. A
-- winner stays pending for the next comparison; two incomparable
-- candidates cause the first one to be emitted immediately.
module Algorithm {A : Set} (Q : A → A → Set) (rr : ∀ x → Q x x)
                 (tr : ∀ {a b c} → Q a b → Q b c → Q a c) where
  open Prune Q rr tr using (Comparison; first; second; retain)
  module Run (cmp : ∀ x y → Comparison x y) where
    pending : A → List A → List A
    pending a [] = a ∷ []
    pending a (b ∷ xs) with cmp a b
    ... | first _ = pending a xs
    ... | second _ = pending b xs
    ... | retain = a ∷ pending b xs

    thinlist : List A → List A
    thinlist [] = []
    thinlist (a ∷ xs) = pending a xs

-- A single bottom element dominates two incomparable alternatives.
data Item : Set where bot l r : Item
data Q : Item → Item → Set where
  same : ∀ {a} → Q a a
  bottom : ∀ {a} → Q bot a
chain : ∀ {a b c} → Q a b → Q b c → Q a c
chain same q = q
chain bottom q = bottom
module P = Prune Q (λ _ → same) chain
cmp : ∀ a b → P.Comparison a b
cmp bot b = P.first bottom
cmp l bot = P.second bottom
cmp r bot = P.second bottom
cmp l l = P.first same
cmp r r = P.first same
cmp l r = P.retain
cmp r l = P.retain
module Adj = Algorithm.Run Q (λ _ → same) chain cmp
module Text = P.Algorithm cmp

shorter = bot ∷ l ∷ r ∷ []
longer = l ∷ r ∷ bot ∷ []
short-adj : Adj.thinlist shorter ≡ bot ∷ []
short-adj = refl
short-text : Text.thinlist shorter ≡ bot ∷ r ∷ []
short-text = refl
long-adj : Adj.thinlist longer ≡ l ∷ bot ∷ []
long-adj = refl
long-text : Text.thinlist longer ≡ bot ∷ []
long-text = refl
