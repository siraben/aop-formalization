{-# OPTIONS --safe --without-K #-}
module AoP.LocaleComposition where

open import AoP.Prelude
open import AoP.LocaleRelations using (Frame; module Rel)

-- Exercise 4.18. Whichever pair of arrows is composed first, a
-- three-edge path has the same two intermediate points. Distribute
-- the outer meet, then inject each path into the opposite nesting.
module Law (F : Frame) where
  open Frame F
  open Rel F
  swap : ∀ a b → meet a b ≤ meet b a
  swap a b = pair (right a b) (left a b)
  distʳ : ∀ {I} a (f : I → V) → meet a (join f) ≤ join (λ i → meet a (f i))
  distʳ a f = chain (swap a (join f)) (chain (distribute f a) (least _ λ i → chain (swap (f i) a) (inject _ i)))

  assoc-in : ∀ {A B C D} (T : Rel D C) (S : Rel C B) (R : Rel B A) → ((T ∘ S) ∘ R) ⊆ (T ∘ (S ∘ R))
  assoc-in T S R d a = least _ λ b → chain (distribute (λ c → meet (T d c) (S c b)) (R b a)) (least _ (path b))
    where path : ∀ b c → meet (meet (T d c) (S c b)) (R b a) ≤ (T ∘ (S ∘ R)) d a
          path b c = chain (pair t (chain (pair s r) (inject _ b))) (inject _ c)
            where ts = left (meet (T d c) (S c b)) (R b a)
                  t = chain ts (left (T d c) (S c b))
                  s = chain ts (right (T d c) (S c b))
                  r = right (meet (T d c) (S c b)) (R b a)
  assoc-out : ∀ {A B C D} (T : Rel D C) (S : Rel C B) (R : Rel B A) → (T ∘ (S ∘ R)) ⊆ ((T ∘ S) ∘ R)
  assoc-out T S R d a = least _ λ c → chain (distʳ (T d c) (λ b → meet (S c b) (R b a))) (least _ (path c))
    where path : ∀ c b → meet (T d c) (meet (S c b) (R b a)) ≤ ((T ∘ S) ∘ R) d a
          path c b = chain (pair (chain (pair t s) (inject _ c)) r) (inject _ b)
            where sr = right (T d c) (meet (S c b) (R b a))
                  s = chain sr (left (S c b) (R b a))
                  r = chain sr (right (S c b) (R b a))
                  t = left (T d c) (meet (S c b) (R b a))
