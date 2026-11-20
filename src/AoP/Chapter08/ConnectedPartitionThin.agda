{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ConnectedPartitionThin where

open import AoP.Common.Prelude
open import AoP.Chapter08.ConnectedBlock using (module Law)
open import AoP.Chapter08.ConnectedBlockExchange using (module Exchange)
open import AoP.Chapter08.ConnectedPartitionMinimum using (module Solver)
open import AoP.Chapter08.Thinning using (Min; Thin)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; split; merge)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter08.ParagraphMinimum using (Dec)

-- Exercise 8.14: the unfused specification. Select one least member
-- per connected block, preserving membership and covering each input
-- occurrence by a retained representative from that very block.
module Select {A : Set} (Q : A → A → Set) (self : ∀ x → Q x x)
  (trans : ∀ {x y z} → Q x y → Q y z → Q x z)
  (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  open Law Q
  open Exchange Q
  open Solver Q self test using (solve; module Result)
  least : ∀ a xs → Connected (a ∷ xs) → Σ A λ w → Min Q w (λ y → y ∈ a ∷ xs)
  least a [] c = a , here , λ { _ here → self a ; _ (there ()) }
  least a (b ∷ xs) c with least b xs (λ x y m n → c x y (there m) (there n))
  ... | w , at , low with c a w here (there at)
  ... | inl le = a , here , λ { _ here → self a ; y (there m) → trans le (low y m) }
  ... | inr le = w , there at , λ { _ here → le ; y (there m) → low y m }
  minima : ∀ {n xs} → Within n xs → List A
  minima empty = []
  minima (cut {a = a} {xs} ok rest) = fst (least a xs ok) ∷ minima rest
  correct : ∀ {n xs} (p : Within n xs) → Thin Q (λ a → a ∈ minima p) (λ a → a ∈ xs)
  Thin.subset (correct empty) ()
  Thin.subset (correct (cut {a = a} {xs} {ys} ok rest)) here = merge (a ∷ xs) ys (inl (fst (snd (least a xs ok))))
  Thin.subset (correct (cut {a = a} {xs} {ys} ok rest)) (there m) = merge (a ∷ xs) ys (inr (Thin.subset (correct rest) m))
  Thin.cover (correct empty) _ ()
  Thin.cover (correct (cut {a = a} {xs} {ys} ok rest)) x m with split (a ∷ xs) ys m
  ... | inl h = _ , here , snd (snd (least a xs ok)) x h
  ... | inr t with Thin.cover (correct rest) x t
  ... | w , member , le = w , there member , le
  thinlist : ∀ xs → Σ (List A) λ ys → Thin Q (λ a → a ∈ ys) (λ a → a ∈ xs)
  thinlist xs = _ , correct (Result.partition (solve xs))
