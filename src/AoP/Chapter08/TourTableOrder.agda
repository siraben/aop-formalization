{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.TourTableOrder where

open import AoP.Common.Prelude
open import AoP.Chapter08.TourArmExtension using (module Step)
open import AoP.Chapter08.TourKeyLayer using (module Keys)
open import AoP.Chapter08.TourArmNormal using (module Law′)
open import AoP.Chapter06.OrderedMeet using (module Order)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; split)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)

-- 8.25. Index the nonempty tail by its last city z; the reverse arm
-- always starts there, so the inductive step cannot lose its witness
-- of nonemptiness. No ordering of the cities is needed.
module Table (City : Set) where
  open Keys City
  open Step City using (Ne)
  Unique = Order.Ordered (Ne {City})
  front : List City → City → List City
  front xs z = xs ++ (z ∷ [])
  rev : List City → List City
  rev [] = []
  rev (x ∷ xs) = rev xs ++ (x ∷ [])

  private
    snocU : ∀ {x} xs → Unique xs → (x ∈ xs → ⊥) → Unique (xs ++ (x ∷ []))
    snocU [] _ fresh = Order.cons (λ ()) Order.nil
    snocU {x} (a ∷ xs) (Order.cons h u) fresh = Order.cons bound (snocU xs u (λ m → fresh (there m)))
      where bound : ∀ {b} → b ∈ (xs ++ (x ∷ [])) → Ne a b
            bound m with split xs (x ∷ []) m
            ... | inl p = h p
            ... | inr here = λ { refl → fresh here }
    member : ∀ xs z {b} → b ∈ (z ∷ rev xs) → b ∈ front xs z
    member [] z here = here
    member (x ∷ xs) z here = there (member xs z here)
    member (x ∷ xs) z (there m) with split (rev xs) (x ∷ []) m
    ... | inl p = there (member xs z (there p))
    ... | inr here = here
    reverseU : ∀ xs z → Unique (front xs z) → Unique (z ∷ rev xs)
    reverseU [] z u = u
    reverseU (x ∷ xs) z (Order.cons h u) = snocU (z ∷ rev xs) (reverseU xs z u) (λ m → h (member xs z m) refl)

  module Compute (eq : ∀ (p q : Key) → (p ≡ q) ⊎ Ne p q) where
    open Step.At City eq using (expand; extend)
    keys : City → List City → City → List Key
    keys b [] z = expand b ((z , z) ∷ [])
    keys b (c ∷ cs) z = expand b (keys c cs z)

    order : ∀ b cs z → Unique (b ∷ front cs z) → keys b cs z ≡ L b (z ∷ rev cs) ++ R b (front cs z)
    order b [] z (Order.cons h u) = Law′.At.normal City eq b (z ∷ []) (z ∷ []) u u (λ m → h m refl)
    order b (c ∷ cs) z (Order.cons h u) rewrite order c cs z u =
      finish cs z (reverseU (c ∷ cs) z u) u (λ m → h (member (c ∷ cs) z m) refl)
      where finish : ∀ ts a → Unique (a ∷ rev (c ∷ ts)) → Unique (front (c ∷ ts) a) →
                     (b ∈ (a ∷ rev (c ∷ ts)) → ⊥) → expand b (L c (a ∷ rev ts) ++ R c (front ts a)) ≡ L b (a ∷ rev (c ∷ ts)) ++ R b (front (c ∷ ts) a)
            finish [] a = extend b c a [] a []
            finish (v ∷ vs) a = extend b c a (rev (v ∷ vs)) v (front vs a)
