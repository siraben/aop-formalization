{-# OPTIONS --safe --without-K #-}
module AoP.ClosedDistributivity where

open import Agda.Primitive using (lzero)
open import AoP.Prelude
open import AoP.Categories using (Category)
open import AoP.DistributiveHoms using (Bijection; module Law)
open import AoP.DistributiveSquare using (module Proof)
open import AoP.InverseNaturality using (module Square)
open import AoP.RepresentingIso using () renaming (module Law to Represent)
open Bijection

-- Exercise 3.32 in the small hom-set model: categorical equality
-- reflects propositional equality of arrows. Currying and splitting
-- are supplied with their ordinary target-naturality laws.
module Law′ {e} (K : Category lzero lzero e) where
  open Category K
  module Data (reflect : ∀ {x y} {f g : Hom x y} → f ≈ g → f ≡ g)
    (sum prod exp : Obj → Obj → Obj)
    (cur : ∀ a b t → Bijection (Hom (prod a b) t) (Hom a (exp b t)))
    (spl : ∀ a b t → Bijection (Hom (sum a b) t) (Hom a t × Hom b t))
    (a b c : Obj)
    (emap : ∀ {s t} → Hom s t → Hom (exp c s) (exp c t)) where
    P = prod (sum a b) c
    Q = sum (prod a c) (prod b c)
    module D t = Law Hom sum prod exp cur spl a b c t
    post : ∀ {s t} → Hom s t → ∀ x → Hom x s → Hom x t
    post u x f = u ∘ f
    module N {s t} (u : Hom s t) = Proof Hom sum prod exp cur spl a b c s t (post u) (post (emap u))
    module Result
      (cn : ∀ {s t} (u : Hom s t) x f → to (cur x c t) (u ∘ f) ≡ emap u ∘ to (cur x c s) f)
      (sn : ∀ {s t} (u : Hom s t) x y f → to (spl x y t) (u ∘ f) ≡ N.pair u (post u x) (post u y) (to (spl x y s) f)) where
      private
        eqv : ∀ {x y} {f g : Hom x y} → f ≡ g → f ≈ g
        eqv refl = reflexive
        forward = λ {s} {t} (u : Hom s t) → N.Squares.natural u (cn u) (sn (emap u) a b) (sn u (prod a c) (prod b c))
        backward = λ {s} {t} (u : Hom s t) → Square.inverse (D.distribute s) (D.distribute t) (post u P) (post u Q) (forward u)
      module Iso = Represent.Identify K P Q (λ {t} → to (D.distribute t)) (λ {t} → from (D.distribute t))
        (λ p → eqv (cong (to (D.distribute _)) (reflect p))) (λ p → eqv (cong (from (D.distribute _)) (reflect p)))
        (λ f → eqv (section (D.distribute _) f)) (λ f → eqv (retract (D.distribute _) f))
        (λ u f → eqv (forward u f)) (λ u f → eqv (backward u f))
