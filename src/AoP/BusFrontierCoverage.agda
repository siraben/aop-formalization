{-# OPTIONS --safe --without-K #-}
module AoP.BusFrontierCoverage where

open import AoP.Prelude
open import AoP.BusProfile
open import AoP.BusLayouts
open import AoP.BusFrontier using (module Generate)
open import AoP.BusProfileDecision using (module Frontier)
open import AoP.Subsequences using (_∈_; here; there; image; merge)
open import AoP.Thinning using (Thin)
open import AoP.Horner using (map)
open import AoP.Naturality using (_++_)
open import AoP.Polynomial using (inl; inr)
open import AoP.NatOrder using (rid; chain)
open import Agda.Builtin.Nat using (Nat; suc)

module Law (js : List Nat) where
  open Generate js
  open Frontier.Thin js using (thinlist; correct)
  Covered : List Stops → Stops → Set
  Covered ls l = Σ Stops λ w → (w ∈ ls) × Profile js w l
  prune : ∀ ls {l} → Covered ls l → Covered (thinlist ls) l
  prune ls (v , m , p) with Thin.cover (correct ls) v m
  ... | w , kept , q = w , kept , λ i n → chain (q i n) (p i n)

  -- Rebuild the competitor one decision at a time. In a take branch
  -- the smaller-quota replacement can be extended by the same stop.
  cover : ∀ {j m k x xs} → Layout j m (suc k) (x ∷ xs) → Covered (build j m k) (sites x xs)
  cover {j} {suc m} {0} (take done) = prune (sites j [] ∷ build (suc j) m 0) {sites j []} (sites j [] , here , λ _ _ → rid _)
  cover {j} {suc m} {0} {x} {xs} (skip p) with cover p
  ... | w , mem , q = prune (sites j [] ∷ build (suc j) m 0) {sites x xs} (w , there mem , q)
  cover {j} {suc m} {suc k} {x} {xs} (skip p) with cover p
  ... | w , mem , q = prune _ {sites x xs} (w , merge (map (add j) (build (suc j) m k)) _ (inr mem) , q)
  cover {j} {suc m} {suc k} {xs = y ∷ ys} (take p) with cover p
  ... | w , mem , q = prune _ {sites j (y ∷ ys)} (add j w , merge _ (build (suc j) m (suc k)) (inl (image (add j) mem)) , extend js j w (sites y ys) q)
  cover {k = suc k} {xs = []} (take p) = absurd-empty p
    where absurd-empty : ∀ {i m n} {A : Set} → Layout i m (suc n) [] → A
          absurd-empty (skip l) = absurd-empty l
