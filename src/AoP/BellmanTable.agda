{-# OPTIONS --safe --without-K #-}
module AoP.BellmanTable where

open import AoP.Prelude
open import AoP.BranchingDP using (module DP)
open import AoP.Thinning using (Min)

-- §9.1. A completed table cell has solved every admissible decomposition.
-- Each decomposition carries the handles of its children; the entry
-- chooses a least evaluation among these alternatives. Prove correctness
-- from the entries themselves, so optimal children need not be assumed.
-- Empty child families represent leaves. A cell for an input with no
-- admissible decomposition cannot be built, since `entry` needs a winner.
module Table {X V S : Set} (P : S → Set)
             (D : X → (s : S) → (P s → X) → Set)
             (f : (s : S) → (P s → V) → V) (_≤_ : V → V → Set)
             (trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
             (mono : ∀ s a b → (∀ i → a i ≤ b i) → f s a ≤ f s b) where
  open DP P D f _≤_ trans mono using (Feasible; build)

  record Split (x : X) : Set where
    constructor split
    field
      shape : S
      sub : P shape → X
      valid : D x shape sub
  open Split

  data Cell (x : X) : V → Set where
    entry : (values : (d : Split x) → P (shape d) → V) →
            (children : ∀ d i → Cell (sub d i) (values d i)) →
            (winner : Split x) →
            (∀ d → f (shape winner) (values winner) ≤ f (shape d) (values d)) →
            Cell x (f (shape winner) (values winner))

  feasible : ∀ {x v} → Cell x v → Feasible x v
  feasible (entry values children d least) =
    build (shape d) (sub d) (valid d) (values d) (λ i → feasible (children d i))

  bound : ∀ {x v w} → Cell x v → Feasible x w → v ≤ w
  bound (entry vals kids win least) (build s sub d g rivals) =
    trans (least alt) (mono s (vals alt) g (λ i → bound (kids alt i) (rivals i)))
    where alt = split s sub d

  correct : ∀ {x v} → Cell x v → Min _≤_ v (Feasible x)
  correct c = feasible c , λ w → bound c
