{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ConnectedPartitionMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter08.ConnectedBlock using (module Law)
open import AoP.Chapter08.ConnectedBlockExchange using (module Exchange)
open import AoP.Chapter08.LongestConnectedBlock using (module Scan)
open import AoP.Chapter07.LongestPrefix using (module Prefix)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import AoP.Chapter05.Subsequences using (here; there)
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
  open import AoP.Chapter08.GreedyBoundaryAgreement using (module Agreement)
  open Agreement Q using (Cuts; stop; take; unique)
  block-list : ∀ {n xs} → Within n xs → List (List A)
  block-list empty = []
  block-list (cut {a = a} {xs = xs} _ p) = (a ∷ xs) ∷ block-list p
  record Result (xs : List A) : Set where
    constructor answer
    field count : Nat
          partition : Within count xs
          least : ∀ n → Within n xs → count ≤ n
          boundaries : Cuts xs (block-list partition)
  install : ∀ {ys zs n} → ys ≡ zs → Within n ys → Within n zs
  install refl w = w
  unchanged : ∀ {ys zs n} (eq : ys ≡ zs) (w : Within n ys) → block-list w ≡ block-list (install eq w)
  unchanged refl w = refl
  -- Fuel is the number of blocks in any known feasible partition.
  -- Exchange decreases it at every recursive call on a nonempty list.
  solve-with : ∀ n xs → Within n xs → Result xs
  solve-with n [] _ = answer 0 empty (λ _ _ → z≤) stop
  solve-with 0 (x ∷ xs) ()
  solve-with (suc n) (x ∷ xs) budget with first (x ∷ xs) in chosen
  ... | result [] rest eq fits dom with dom (cons nil) (singleton x)
  ...   | ()
  solve-with (suc n) (x ∷ xs) budget | g@(result (a ∷ bs) rest eq fits dom) with solve-with n rest (exchange g budget)
  ... | answer k p low cuts = answer (suc k) (install eq (cut fits p)) min-bound (shift (unchanged eq (cut fits p)) (take g cuts))
    where shift : ∀ {bs cs} → bs ≡ cs → Cuts (x ∷ xs) bs → Cuts (x ∷ xs) cs
          shift refl w = w
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
  agrees : ∀ xs {bs} → Cuts xs bs → bs ≡ block-list (Result.partition (solve xs))
  agrees xs w = unique w (Result.boundaries (solve xs))
