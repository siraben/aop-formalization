{-# OPTIONS --safe --without-K #-}
module AoP.TourCostedOrder where

open import AoP.Prelude
open import AoP.TourNext using (module Legs)
open import AoP.TourThinProjection using (module Law)
open import AoP.TourKeyLayer using (module Keys)
open import AoP.TourTableOrder using (module Table)
open import AoP.TourArmExtension using (module Step)
open import AoP.Polynomial using (_⊎_)
open import AoP.Complement using (⊥)
open import AoP.Horner using (map)
open import AoP.Naturality using (_++_; map-++)
open import Agda.Builtin.Nat using (Nat)

-- Run the thinning calculation on tours with both leg tails present.
-- Index a frontier by its common first city, so a newly prepended city
-- changes the index. The choice of score cannot affect the key order.
module Solve (City : Set) where
  open Legs City
  open Keys City
  At : City → Set
  At b = Σ Tour λ t → Tour.first t ≡ b
  key : ∀ {b} → At b → Key
  key p = next (fst p)
  addL addR : ∀ a {b} → At b → At a
  addL a (legs b l r ls rs , refl) = dropl a (legs b l r ls rs) , refl
  addR a (legs b l r ls rs , refl) = dropr a (legs b l r ls rs) , refl

  module Run (cost : Tour → Nat) (eq : ∀ (k j : Key) → (k ≡ j) ⊎ (k ≡ j → ⊥)) where
    module K = Table.Compute City eq
    module P b = Law (key {b}) (λ p → cost (fst p)) eq
    grow : ∀ a {b} → List (At b) → List (At a)
    grow a ts = P.thin a (map (addL a) ts ++ map (addR a) ts)
    private
      lefts : ∀ a b (ts : List (At b)) → map key (map (addL a) ts) ≡ map (left b) (map key ts)
      lefts a b [] = refl
      lefts a b ((legs .b l r ls rs , refl) ∷ ts) = cong ((l , b) ∷_) (lefts a b ts)
      rights : ∀ a b (ts : List (At b)) → map key (map (addR a) ts) ≡ map (right b) (map key ts)
      rights a b [] = refl
      rights a b ((legs .b l r ls rs , refl) ∷ ts) = cong ((b , r) ∷_) (rights a b ts)
    layer : ∀ a b (ts : List (At b)) → map key (grow a ts) ≡ Step.At.expand City eq b (map key ts)
    layer a b ts = P.projection a (map (addL a) ts ++ map (addR a) ts) ∙ cong (P.compact a) (map-++ key (map (addL a) ts) (map (addR a) ts) ∙
      cong (λ xs → xs ++ map key (map (addR a) ts)) (lefts a b ts) ∙ cong (map (left b) (map key ts) ++_) (rights a b ts))
    tours : ∀ a b → List City → City → List (At a)
    tours a b [] z = grow a ((legs b z z [] [] , refl) ∷ [])
    tours a b (c ∷ cs) z = grow a (tours b c cs z)
    erase : ∀ a b cs z → map key (tours a b cs z) ≡ K.keys b cs z
    erase a b [] z = layer a b ((legs b z z [] [] , refl) ∷ [])
    erase a b (c ∷ cs) z = layer a b (tours b c cs z) ∙ cong (Step.At.expand City eq b) (erase b c cs z)
    order : ∀ a b cs z → Table.Unique City (b ∷ Table.front City cs z) →
            map key (tours a b cs z) ≡ L b (z ∷ Table.rev City cs) ++ R b (Table.front City cs z)
    order a b cs z u = erase a b cs z ∙ K.order b cs z u
