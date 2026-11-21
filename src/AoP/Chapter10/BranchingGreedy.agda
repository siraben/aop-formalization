{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.BranchingGreedy where

open import AoP.Common.Prelude
open import AoP.Chapter09.BranchingDP using (module DP)
open import AoP.Chapter08.Thinning using (Min)

-- §10.1. After selecting a decomposition, solve each of its children
-- greedily. A competitor can use a completely different shape. Exchange
-- must replace its whole solution by a completion of the chosen shape
-- whose cost is no higher. This is the obligation that justifies pruning
-- all other decompositions before their children have been solved.
module Trees {X V S : Set} (P : S → Set)
             (D : X → (s : S) → (P s → X) → Set)
             (f : (s : S) → (P s → V) → V) (_≤_ : V → V → Set)
             (trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
             (mono : ∀ s a b → (∀ i → a i ≤ b i) → f s a ≤ f s b) where
  open DP P D f _≤_ trans mono using (Feasible; build)

  Exchange : ∀ x s → (P s → X) → Set
  Exchange x s sub = ∀ v → Feasible x v →
    Σ (P s → V) λ g → ((i : P s) → Feasible (sub i) (g i)) × (f s g ≤ v)

  data Greedy (x : X) : V → Set where
    choose : ∀ s sub → D x s sub → Exchange x s sub → ∀ a →
             (∀ i → Greedy (sub i) (a i)) → Greedy x (f s a)

  valid : ∀ {x v} → Greedy x v → Feasible x v
  valid (choose s sub d ex a kids) = build s sub d a (λ i → valid (kids i))

  lower : ∀ {x u v} → Greedy x u → Feasible x v → u ≤ v
  lower {v = v} (choose s sub d ex a kids) competitor with ex v competitor
  ... | b , completions , le =
    f s a ≤⟨ local ⟩       -- solve the exchanged competitor's children greedily
    f s b ≤⟨ le ⟩∎ v       -- exchange bounds this completion by the original rival
    where
    open BoundSteps _≤_ trans
    local : f s a ≤ f s b
    local = mono s a b (λ i → lower (kids i) (completions i))

  minimum : ∀ {x v} → Greedy x v → Min _≤_ v (Feasible x)
  minimum g = valid g , λ _ → lower g
