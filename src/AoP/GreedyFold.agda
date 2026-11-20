{-# OPTIONS --safe --without-K #-}
module AoP.GreedyFold where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)

-- §7.2, Theorem 7.2 for cons-lists. A nondeterministic fold can keep
-- many partial answers. When is it safe to keep only a local minimum?
-- If a discarded tail could take a step, a better retained tail must
-- be able to match that step with no worse output. This is simulation,
-- not just monotonicity of a deterministic cost function.
module Lists {A B : Set} (_≤_ : B ← B)
             (trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
             (E : B → Set) (F : B ← (A × B))
             (match : ∀ {x b c z} → b ≤ c → F z (x , c) →
                      Σ B λ y → F y (x , b) × (y ≤ z)) where
  -- Each constructor records both local feasibility and local optimality.
  -- With ties there can be several greedy runs; the theorem covers all.
  data Greedy : B ← List A where
    seed : ∀ {b} → Min _≤_ b E → Greedy b []
    step : ∀ {x xs b y} → Greedy b xs → Min _≤_ y (λ z → F z (x , b)) → Greedy y (x ∷ xs)

  feasible : ∀ {xs y} → Greedy y xs → Fold E F y xs
  feasible (seed (e , _)) = nil e
  feasible (step g (f , _)) = cons f (feasible g)

  bound : ∀ {xs y z} → Greedy y xs → Fold E F z xs → y ≤ z
  bound (seed (_ , best)) (nil e) = best _ e
  bound (step g (_ , best)) (cons f tail) with match (bound g tail) f
  ... | y′ , available , le = trans (best y′ available) le

  optimum : ∀ {xs y} → Greedy y xs → Min _≤_ y (λ z → Fold E F z xs)
  optimum g = feasible g , λ z → bound g
