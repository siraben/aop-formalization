{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.BranchingDP where

open import AoP.Common.Prelude
open import AoP.Chapter08.Thinning using (Min)

-- §9.1. A decomposition chooses a shape (for example a split point)
-- and supplies one child problem for each position in that shape. These
-- positions may depend on the shape: a leaf has none, a fork has two.
-- For a fixed decomposition the cost algebra is monotone in the entire
-- family of child results. Compare the minima across decompositions only
-- after extending their optimal child families.
module DP {Input Value Shape : Set} (Pos : Shape → Set)
          (Decomp : (x : Input) (s : Shape) → (Pos s → Input) → Set)
          (eval : (s : Shape) → (Pos s → Value) → Value)
          (_≤_ : Value → Value → Set)
          (trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
          (mono : ∀ s f g → (∀ i → f i ≤ g i) → eval s f ≤ eval s g) where

  -- Membership is a tree of successful decompositions. Keeping the
  -- witnesses makes feasibility explicit even for a partial decomposition.
  data Feasible (x : Input) : Value → Set where
    build : ∀ s children → Decomp x s children → ∀ f →
            (∀ i → Feasible (children i) (f i)) → Feasible x (eval s f)

  record Candidate (x : Input) (v : Value) : Set where
    constructor candidate
    field
      shape : Shape
      sub : Pos shape → Input
      split : Decomp x shape sub
      result : Pos shape → Value
      minima : ∀ i → Min _≤_ (result i) (Feasible (sub i))
      value : eval shape result ≡ v

  -- Assume a minimum exists for each child of each successful competitor.
  -- The caller supplies the family of witnesses (no choice axiom). The
  -- proof first establishes feasibility, then chains the two inequalities.
  bellman : ∀ x → (∀ s sub → Decomp x s sub → ∀ i → Σ Value λ w → Min _≤_ w (Feasible (sub i))) →
            ∀ v → Min _≤_ v (Candidate x) → Min _≤_ v (Feasible x)
  bellman x best v (candidate s sub split f opts refl , least) =
    build s sub split f (λ i → fst (opts i)) , bound
    where
    bound : ∀ w → Feasible x w → eval s f ≤ w
    bound _ (build t cs d g runs) = trans local extended
      where
      opt = best t cs d
      costs = λ i → fst (opt i)
      local : eval s f ≤ eval t costs
      local = least _ (candidate t cs d costs (λ i → snd (opt i)) refl)
      extended : eval t costs ≤ eval t g
      extended = mono t costs g (λ i → snd (snd (opt i)) (g i) (runs i))
