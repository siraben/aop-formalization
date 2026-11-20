{-# OPTIONS --safe --without-K #-}
module AoP.LayeredCachedTable where

open import AoP.Prelude
open import AoP.LayeredCostFold using (module Paths)
open import AoP.LayeredPathMinimum using (module Solver)
open import AoP.LayeredCachedRow using (module Row)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.NatOrder using (_≤_; rid; chain; sum-mono)
open import Agda.Builtin.Nat using (Nat)

-- Compose the cached scans over the original layer and path types.
-- For each legal rival store a representative with the same head:
-- only then will prepending the next vertex charge the same edge.
module Build {V : Set} (wt : V → V → Nat) where
  open Solver wt using (Layers; before; last; Legal; extend; finish; tab; source; member; Answer)
  open Row wt using (Cell; end; module At)
  open Paths wt using (Path; cost; head; via; single)
  open Cell
  record Table (t : Layers) : Set where
    constructor rows
    field c : Cell
          cs : List Cell
          legal : ∀ {q} → q ∈ c ∷ cs → Legal t (path q)
          cover : ∀ r → Legal t r → Σ Cell λ q → (q ∈ c ∷ cs) × ((head (path q) ≡ head r) × (cost (path q) ≤ cost r))
  build : ∀ t → Table t
  build (last v vs) = rows (end v) (tab end vs) ok keep
    where ok : ∀ {q} → q ∈ tab end (v ∷ vs) → Legal (last v vs) (path q)
          ok m with source end (v ∷ vs) m
          ... | a , at , refl = finish at
          keep : ∀ r → Legal (last v vs) r → _
          keep .(single _) (finish at) = _ , member end at , refl , rid _
  build (before v vs t) with build t
  ... | rows c cs ok keep = rows (new v) (tab new vs) legal cover
    where
      module P a = At.Pick a c cs
      new = λ a → P.output a
      legal : ∀ {q} → q ∈ tab new (v ∷ vs) → Legal (before v vs t) (path q)
      legal m with source new (v ∷ vs) m
      ... | a , at , refl = extend at (ok (P.chosen a))
      cover : ∀ r → Legal (before v vs t) r → _
      cover .(via _ _) (extend {a = a} {p = r} at route) with keep r route
      ... | q , m , eq , bound = new a , member new at , refl , chain (P.beats a q m) (lift eq bound)
        where lift : head (path q) ≡ head r → cost (path q) ≤ cost r → cost (via a (path q)) ≤ cost (via a r)
              lift e b rewrite e = sum-mono (rid _) b

  -- Compare final cells by stored score. Use exact-cost only in the
  -- proof: the scan never needs to sum an already represented path.
  open import AoP.LeftmostMinimumFold using (module Fold)
  open import AoP.NatOrder using (compare)
  module Final = Fold (λ x y → score x ≤ score y) (λ x → rid _) chain
    (λ x y → compare _ _) (λ x y → Row.decide wt _ _)
  solve : ∀ t → Answer t
  solve t with build t
  ... | rows c cs ok keep = path w , ok (fst best) , bound
    where result = Final.scan c cs
          w = Final.Winner.value result
          best = Final.Winner.minimum result
          bound : ∀ r → Legal t r → cost (path w) ≤ cost r
          bound r legal with keep r legal
          ... | q , at , _ , lb = chain (price w q (snd best q at)) lb
            where price : ∀ x y → score x ≤ score y → cost (path x) ≤ cost (path y)
                  price x y p rewrite exact-cost x | exact-cost y = p

module Trace where
  open import AoP.LayeredCostFold using (weight; root; east; goal)
  open import AoP.LayeredPathMinimum using (module Example)
  route : fst (Build.solve weight Example.network) ≡ Paths.via root (Paths.via east (Paths.single goal))
  route = refl
