{-# OPTIONS --safe --without-K #-}
module AoP.VanService where

open import AoP.Prelude
open import AoP.Reserves
open import AoP.SecureBlock
open import AoP.LongestPrefix
open import AoP.VanTrimming
open import AoP.VanMinimum
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §7.5. A van may reset the reserve before each transaction. This makes
-- singleton feasibility an exact test for serviceability: a failed
-- singleton rules out every partition containing that transaction.
module Service (cap : Nat) where
  open Bank cap
  open Trim cap
  open Prefix {Tx}
  open Minimum cap

  len : List Tx → Nat
  len [] = 0
  len (_ ∷ xs) = suc (len xs)

  Impossible : List Tx → Set
  Impossible xs = ∀ {n} → Within n xs → ⊥

  first : ∀ {t ts n} → Within n (t ∷ ts) → Secure (t ∷ [])
  first (block (a , b , run) rest) = a , Van.truncate cap (cons nil) run

  singletons : ∀ xs → Within (len xs) xs ⊎ Impossible xs
  singletons [] = inl done
  singletons (t ∷ ts) with Check.secure? cap (t ∷ [])
  ... | inr no = inr λ p → no (first p)
  ... | inl fits with singletons ts
  ...   | inr no = inr λ p → no (drop-one p)
  ...   | inl rest = inl (block {ts = []} fits rest)

  schedule : ∀ xs → Opt xs ⊎ Impossible xs
  schedule xs with singletons xs
  ... | inr no = inr no
  ... | inl p = inl (solve (len xs) p)
