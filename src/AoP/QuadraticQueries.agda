{-# OPTIONS --safe --without-K #-}
module AoP.QuadraticQueries where

open import AoP.Prelude
open import AoP.Subsequences using (_∈_; here; there; preimage; split)
open import AoP.Horner using (map)
open import AoP.Naturality using (_++_)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import AoP.TraceCardinality using (module Count)
open Count
open import AoP.PairMembers using (module Members)
open import AoP.OrderedPairs using (pairs; count; pred)
open import AoP.NatOrder using (_≤_)
open import AoP.ConversionCost using (len)
open import Agda.Builtin.Nat using (_*_)
open import AoP.HiddenTrace using (module Law)
open import AoP.MinimalQueries using (module Solver)

mapped : ∀ {A B : Set} (f : A → B) → (∀ {a b} → f a ≡ f b → a ≡ b) → ∀ {xs} → Distinct xs → Distinct (map f xs)
mapped f inj nil = nil
mapped f inj (cons {a} {xs} fresh d) = cons absent (mapped f inj d)
  where absent : f a ∈ map f xs → ⊥
        absent m with preimage f xs m
        ... | y , old , eq with inj eq
        ...   | refl = fresh old

join : ∀ {A : Set} {xs ys : List A} → Distinct xs → Distinct ys → (∀ a → a ∈ xs → a ∈ ys → ⊥) → Distinct (xs ++ ys)
join nil dy dis = dy
join (cons {a} {xs} fresh dx) dy dis = cons absent (join dx dy (λ b m → dis b (there m)))
  where absent : _
        absent m with split xs _ m
        ... | inl p = fresh p
        ... | inr p = dis a here p

-- Separate the three parts by the position of the fresh head: first
-- coordinate, second coordinate, or neither. Within each new part
-- the other coordinate determines the pair uniquely.
unique : ∀ {A : Set} {xs : List A} → Distinct xs → Distinct (pairs xs)
unique nil = nil
unique {A} (cons {x} {xs} fresh d) = join left (join right (unique d) right-old) left-rest
  where
  L = map (x ,_) xs
  R = map (_, x) xs
  left = mapped (x ,_) (cong snd) d
  right = mapped (_, x) (cong fst) d
  right-old : ∀ q → q ∈ R → q ∈ pairs xs → ⊥
  right-old q m old with preimage (_, x) xs m
  ... | y , _ , refl = fresh (fst (snd (Members.endpoints d old)))
  left-rest : ∀ q → q ∈ L → q ∈ (R ++ pairs xs) → ⊥
  left-rest q m rest with preimage (x ,_) xs m
  ... | y , _ , refl with split R (pairs xs) rest
  ...   | inr old = fresh (fst (Members.endpoints d old))
  ...   | inl r with preimage (_, x) xs r
  ...     | _ , bad , refl = fresh bad

module Lower {A : Set} (dec : ∀ (x y : A) → (x ≡ y) ⊎ (x ≡ y → ⊥)) (xs : List A) (d : Distinct xs) where
  open Law dec
  open Solver dec xs
  queries : ∀ p → Correct p → len xs * pred (len xs) ≤ len (T.trace equal p)
  queries p ok with len (pairs xs) | count xs | bound (unique d) (Members.Required.includes dec xs d p ok)
  ... | _ | refl | h = h
