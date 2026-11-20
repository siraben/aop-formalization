{-# OPTIONS --safe --without-K #-}
module AoP.Greedy where

open import AoP.Prelude
open import AoP.Thinning using (Min)
open import AoP.Bellman using (module Choices)

-- §10.1, unary decomposition case. Unlike the Bellman table, the greedy
-- program only needs an optimum for its chosen branch. The exchange law
-- must account for *every* feasible completion of every discarded branch.
module Branch {I V : Set} (_≤_ : V → V → Set)
              (trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
              (child : I → V → Set) (extend : I → V → V)
              (mono : ∀ i {u v} → u ≤ v → extend i u ≤ extend i v)
              (g : I) where
  open Choices _≤_ trans child extend mono using (Feasible)

  Exchange : Set
  Exchange = ∀ i u → child i u → Σ V λ w → child g w × (extend g w ≤ extend i u)

  infixr 2 _≤⟨_⟩_
  _≤⟨_⟩_ : (x : V) {y z : V} → x ≤ y → y ≤ z → x ≤ z
  _ ≤⟨ p ⟩ q = trans p q

  greedy : Exchange → ∀ {v} → Min _≤_ v (child g) → Min _≤_ (extend g v) Feasible
  greedy exchange {v} (valid , least) = (g , v , valid , refl) , optimal
    where
    optimal : ∀ z → Feasible z → extend g v ≤ z
    optimal _ (i , u , admissible , refl) with exchange i u admissible
    ... | w , chosen , dominates =
      extend g v ≤⟨ mono g (least w chosen) ⟩
      dominates  -- extend g w ≤ extend i u, by exchange
