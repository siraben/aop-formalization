{-# OPTIONS --safe --without-K #-}
module AoP.ConnectedPartitionMinimum where

open import AoP.Prelude
open import AoP.Naturality using (_++_)
open import AoP.ConnectedBlock using (module Law)
open import AoP.ConnectedBlockExchange using (module Exchange)
open import AoP.LongestConnectedBlock using (module Scan)
open import AoP.LongestPrefix using (module Prefix)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import AoP.Subsequences using (here; there)
open import Agda.Builtin.Nat using (Nat; suc)

module Solver {A : Set} (Q : A → A → Set) (self : ∀ x → Q x x) (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  open Law Q
  open Exchange Q
  open Scan Q self test using (first)
  open Prefix {A}
  singleton : ∀ x → Connected (x ∷ [])
  singleton x .x .x here here = inl (self x)
  singleton x _ _ here (there ())
  singleton x _ _ (there ()) _
  record Result (xs : List A) : Set where
    constructor answer
    field count : Nat
          partition : Within count xs
          least : ∀ n → Within n xs → count ≤ n
  block-list : ∀ {n xs} → Within n xs → List (List A)
  block-list empty = []
  block-list (cut {a = a} {xs = xs} _ p) = (a ∷ xs) ∷ block-list p
  -- Fuel is the number of blocks in any known feasible partition.
  -- Exchange decreases it at every recursive call on a nonempty list.
  solve-with : ∀ n xs → Within n xs → Result xs
  solve-with n [] _ = answer 0 empty (λ _ _ → z≤)
  solve-with 0 (x ∷ xs) ()
  solve-with (suc n) (x ∷ xs) budget with first (x ∷ xs) in chosen
  ... | result [] rest eq fits dom with dom (cons nil) (singleton x)
  ...   | ()
  solve-with (suc n) (x ∷ xs) budget | g@(result (a ∷ bs) rest eq fits dom) with solve-with n rest (exchange g budget)
  ... | answer k p low = answer (suc k) (install eq (cut fits p)) min-bound
    where install : ∀ {ys zs n} → ys ≡ zs → Within n ys → Within n zs
          install refl w = w
          min-bound : ∀ m → Within m (x ∷ xs) → suc k ≤ m
          min-bound 0 ()
          min-bound (suc m) rival = s≤ (low m (exchange g rival))
  singles : ∀ xs → Σ Nat λ n → Within n xs
  singles [] = 0 , empty
  singles (x ∷ xs) with singles xs
  ... | n , p = suc n , cut {xs = []} (singleton x) p
  solve : ∀ xs → Result xs
  solve xs with singles xs
  ... | n , p = solve-with n xs p
