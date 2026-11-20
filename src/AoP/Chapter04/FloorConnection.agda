{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.FloorConnection where

open import AoP.Common.Prelude

-- Exercise 4.38. With the usual orders on integers and rationals, the
-- lower adjoint embeds an integer as a rational and the upper adjoint
-- rounds a rational down. Below are the precise hypotheses the proof
-- uses. They separate the order argument from a rational representation.
module Law {Z Q : Set} (_≤z_ : Z → Z → Set) (_≤q_ : Q → Q → Set)
           (rid : ∀ z → z ≤z z) (trans : ∀ {p q r} → p ≤q q → q ≤q r → p ≤q r)
           (embed : Z → Q) (floor : Q → Z)
           (mono : ∀ {z w} → z ≤z w → embed z ≤q embed w) where
  Below = ∀ q → embed (floor q) ≤q q
  Greatest = ∀ z q → embed z ≤q q → z ≤z floor q
  Adjunction = ∀ z q → ((embed z ≤q q) → z ≤z floor q) × ((z ≤z floor q) → embed z ≤q q)

  connect : Below → Greatest → Adjunction
  connect below greatest z q = greatest z q , λ p → trans (mono p) (below q)

  below : Adjunction → Below
  below adj q = snd (adj (floor q) q) (rid (floor q))
  greatest : Adjunction → Greatest
  greatest adj z q = fst (adj z q)

  floor-mono : Adjunction → ∀ {q r} → q ≤q r → floor q ≤z floor r
  floor-mono adj {q} {r} le = greatest adj (floor q) r (trans (below adj q) le)
