{-# OPTIONS --safe --without-K #-}
module AoP.VanSolverAgreement where

open import AoP.Prelude
open import AoP.Reserves using (Tx)
open import AoP.VanSchedule using (module Schedule)
open import AoP.VanFold using (module Fold)
open import AoP.CachedVan using (module Cached)
open import AoP.CachedVanOptimal using (module Certificate)
open import AoP.VanRefinement using (module Refine)
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

-- The exhaustive and directional solvers can place visits at different
-- gaps. Their optimality certificates force the same number of visits.
module Compare (cap : Nat) where
  open Schedule cap
  open Fold cap using (Serviceable)
  module C = Cached cap
  private
    antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
    antisym z≤ z≤ = refl
    antisym (s≤ p) (s≤ q) = cong suc (antisym p q)

  Agrees : ∀ {t ts} → Nat → Answer t ts → Set
  Agrees n (impossible _) = ⊥
  Agrees n (optimal q _ _ _) = n ≡ visits q

  agrees : ∀ t ts (s : Serviceable (t ∷ ts)) (ans : Answer t ts) →
           Agrees (visits (C.Result.plan (C.solve t ts s))) ans
  agrees t ts s (impossible no) = no _ (C.Result.partition r) (C.Result.valid r)
    where r = C.solve t ts s
  agrees t ts s (optimal q part ok best) = antisym
    (Certificate.optimality cap t ts s q part ok) (best _ (C.Result.partition r) (C.Result.valid r))
    where r = C.solve t ts s

  exhaustive : ∀ t ts (s : Serviceable (t ∷ ts)) → Agrees (visits (C.Result.plan (C.solve t ts s))) (solve t ts)
  exhaustive t ts s = agrees t ts s (solve t ts)
  longest-prefix : ∀ t ts (s : Serviceable (t ∷ ts)) → Agrees (visits (C.Result.plan (C.solve t ts s))) (Refine.greedy cap t ts)
  longest-prefix t ts s = agrees t ts s (Refine.greedy cap t ts)
