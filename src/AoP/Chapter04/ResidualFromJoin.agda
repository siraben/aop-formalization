{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.ResidualFromJoin where

open import AoP.Common.Prelude

-- §4.4. Fix the right operand of meet or composition. Call the
-- resulting operation apply. A candidate X is admissible at S when
-- apply X lies below S. The join of all such candidates is the largest
-- admissible one, provided apply distributes over that join.
module Law (A B : Set) (_≤a_ : A → A → Set) (_≤b_ : B → B → Set)
  (trans-b : ∀ {x y z} → x ≤b y → y ≤b z → x ≤b z)
  (apply : A → B) (mono : ∀ {x y} → x ≤a y → apply x ≤b apply y)
  (join : ∀ {I : Set} → (I → A) → A) (joinB : ∀ {I : Set} → (I → B) → B)
  (inject : ∀ {I} (p : I → A) i → p i ≤a join p)
  (bound : ∀ {I} (p : I → B) s → (∀ i → p i ≤b s) → joinB p ≤b s)
  (distribute : ∀ {I} (p : I → A) → apply (join p) ≤b joinB (λ i → apply (p i))) where
  Candidate : B → Set
  Candidate s = Σ A (λ x → apply x ≤b s)
  value : ∀ {s} → Candidate s → A
  value = fst
  residual : B → A
  residual s = join (value {s})

  introduce : ∀ x s → apply x ≤b s → x ≤a residual s
  introduce x s admissible = inject (value {s}) (x , admissible)

  -- After distributing, every summand has a bound: it is exactly the
  -- second field of that candidate. Hence the join still meets the test.
  private
    infixr 2 _≤⟨_⟩_
    _≤⟨_⟩_ : (u : B) → ∀ {v w} → u ≤b v → v ≤b w → u ≤b w
    _ ≤⟨ uv ⟩ vw = trans-b uv vw
    infix 3 last-step
    last-step : (u v : B) → u ≤b v → u ≤b v
    last-step u v proof = proof
    syntax last-step u v proof = u ≤⟨ proof ⟩∎ v

  admissible : ∀ s → apply (residual s) ≤b s
  admissible s =
    apply (join (value {s}))         ≤⟨ distribute (value {s}) ⟩
    -- Bound the join by bounding each term with its membership evidence.
    joinB (λ i → apply (value {s} i)) ≤⟨ bound _ s snd ⟩∎ s

  eliminate : ∀ x s → x ≤a residual s → apply x ≤b s
  eliminate x s below =
    apply x ≤⟨ mono below ⟩
    apply (residual s) ≤⟨ admissible s ⟩∎ s

  -- If the budget s is relaxed to t, its largest admissible candidate
  -- is still admissible. Introduce it into the new join. This uses
  -- neither antisymmetry nor a decision procedure on candidates.
  monotone-residual : ∀ s t → s ≤b t → residual s ≤a residual t
  monotone-residual s t relax = introduce (residual s) t test
    where test : apply (residual s) ≤b t
          test = apply (residual s) ≤⟨ admissible s ⟩
                 s                  ≤⟨ relax ⟩∎ t
