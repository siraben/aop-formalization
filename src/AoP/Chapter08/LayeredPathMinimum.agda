{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.LayeredPathMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter08.LayeredCostFold using (module Paths)
open import AoP.Chapter08.LayeredRowChoice using (module Row)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Common.NatOrder using (_≤_; rid; compare; chain)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Common.FiniteMinimum using (module Search)
open import Agda.Builtin.Nat using (Nat)

-- §8.2. A layer has a first vertex and a finite tail. Preserve this
-- nonemptiness in the table so choosing a suffix needs no sentinel.
module Solver {V : Set} (weight : V → V → Nat) where
  open Paths weight
  data Layers : Set where
    last : V → List V → Layers
    before : V → List V → Layers → Layers
  data Legal : Layers → Path → Set where
    finish : ∀ {v vs a} → a ∈ v ∷ vs → Legal (last v vs) (single a)
    extend : ∀ {v vs t a p} → a ∈ v ∷ vs → Legal t p → Legal (before v vs t) (via a p)
  record Table (t : Layers) : Set where
    constructor rows
    field p : Path
          ps : List Path
          legal : ∀ {q} → q ∈ p ∷ ps → Legal t q
          cover : ∀ r → Legal t r → Σ Path λ q → (q ∈ p ∷ ps) × ((head q ≡ head r) × (cost q ≤ cost r))
  open Table
  tab : ∀ {B : Set} → (V → B) → List V → List B
  tab f [] = []
  tab f (x ∷ xs) = f x ∷ tab f xs
  member : ∀ {B : Set} (f : V → B) {x xs} → x ∈ xs → f x ∈ tab f xs
  member f here = here
  member f (there m) = there (member f m)
  source : ∀ {B : Set} (f : V → B) (xs : List V) {b} → b ∈ tab f xs → Σ V λ v → (v ∈ xs) × (f v ≡ b)
  source f (_ ∷ xs) here = _ , here , refl
  source f (_ ∷ xs) (there m) with source f xs m
  ... | v , at , eq = v , there at , eq
  build : ∀ t → Table t
  build (last v vs) = rows (single v) (tab single vs) ok keep
    where ok : ∀ {q} → q ∈ tab single (v ∷ vs) → Legal (last v vs) q
          ok m with source single (v ∷ vs) m
          ... | a , at , refl = finish at
          keep : ∀ r → Legal (last v vs) r → _
          keep .(single _) (finish at) = _ , member single at , refl , rid _
  build (before v vs t) with build t
  ... | rows p ps legal cover = rows (new v) (tab new vs) ok keep
    where
    win = λ a → Row.choose weight a p ps
    new = λ a → via a (Row.Best.suffix (win a))
    ok : ∀ {q} → q ∈ tab new (v ∷ vs) → Legal (before v vs t) q
    ok m with source new (v ∷ vs) m
    ... | a , at , refl = extend at (legal (Row.Best.member (win a)))
    keep : ∀ r → Legal (before v vs t) r → _
    keep .(via _ _) (extend {a = a} {p = r} at route) = new a , member new at , refl , Row.complete weight a (win a) r (cover r route)
  Answer : Layers → Set
  Answer t = Σ Path λ p → Legal t p × (∀ r → Legal t r → cost p ≤ cost r)
  solve : ∀ t → Answer t
  solve t with build t
  ... | rows p ps ok represented with Search.scan (λ (_ : Path) → ⊤) (λ _ → inl tt) cost (p ∷ ps)
  ...   | Search.none no with no p here tt
  ...     | ()
  solve t | rows p ps ok represented | Search.best w at _ least = w , ok at , lower
    where lower : ∀ r → Legal t r → cost w ≤ cost r
          lower r route with represented r route
          ... | q , m , _ , le = chain (least q m tt) le

module Example where
  open import AoP.Chapter08.LayeredCostFold using (weight; root; west; east; goal)
  open Solver weight
  network = before root [] (before west (east ∷ []) (last goal []))
  route : fst (solve network) ≡ Paths.via root (Paths.via east (Paths.single goal))
  route = refl
