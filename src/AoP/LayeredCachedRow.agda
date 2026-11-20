{-# OPTIONS --safe --without-K #-}
module AoP.LayeredCachedRow where

open import AoP.Prelude
open import AoP.LayeredCostFold using (module Paths)
open import AoP.LeftmostMinimumFold using (module Fold)
open import AoP.Subsequences using (_∈_)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; chain; compare)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- §8.2. Compare suffixes for a particular incoming vertex. Package
-- each path with its cached fields and an invariant so that *every*
-- row winner can be passed directly to the next row scan.
module Row {V : Set} (wt : V → V → Nat) where
  open Paths wt using (Path; head; cost; single; via)
  record Cell : Set where
    constructor cell
    field path : Path
          start : V
          score : Nat
          exact-head : start ≡ head path
          exact-cost : score ≡ cost path
  open Cell
  end : V → Cell
  end v = cell (single v) v 0 refl refl
  extend : V → Cell → Cell
  extend v (cell p b n h e) = cell (via v p) v (wt v b + n) refl
    (cong (λ k → wt v k + n) h ∙ cong (wt v (head p) +_) e)

  key : V → Cell → Nat
  key v c = wt v (start c) + score c
  exact : ∀ v c → key v c ≡ cost (via v (path c))
  exact v (cell p .(head p) .(cost p) refl refl) = refl

  decide : ∀ x y → (x ≤ y) ⊎ (x ≤ y → ⊥)
  decide zero y = inl z≤
  decide (suc x) zero = inr (λ ())
  decide (suc x) (suc y) with decide x y
  ... | inl p = inl (s≤ p)
  ... | inr no = inr (λ { (s≤ p) → no p })

  module At (v : V) where
    open Fold (λ a b → key v a ≤ key v b) (λ a → rid _) chain
      (λ a b → compare _ _) (λ a b → decide _ _) using (scan; Winner)
    module W = Winner
    module Pick (c : Cell) (cs : List Cell) where
      best = scan c cs
      suffix = W.value best
      chosen : suffix ∈ c ∷ cs
      chosen = fst (W.minimum best)
      output = extend v suffix
      optimal : ∀ q → q ∈ c ∷ cs → key v suffix ≤ key v q
      optimal = snd (W.minimum best)
      -- Turn the cached-key comparison back into the path specification.
      beats : ∀ q → q ∈ c ∷ cs → cost (via v (path suffix)) ≤ cost (via v (path q))
      beats q m = transport (exact v suffix) (exact v q) (optimal q m)
        where transport : ∀ {a b c d : Nat} → a ≡ b → c ≡ d → a ≤ c → b ≤ d
              transport refl refl p = p

module Trace where
  open import AoP.LayeredCostFold using (weight; root; west; east; goal)
  open Row weight
  module Scan = At.Pick root (extend west (end goal)) (extend east (end goal) ∷ [])
  cached-winner : Cell.score Scan.output ≡ 6
  cached-winner = refl
