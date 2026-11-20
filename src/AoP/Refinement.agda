{-# OPTIONS --safe --without-K #-}
module AoP.Refinement where

open import AoP.Prelude
open import AoP.Folds
open import AoP.Relations

private variable A B C : Set

graph : (A → B) → B ← A
graph f b a = f a ≡ b

-- Implementation refines specification: every computed output is allowed.
-- The graph of a total function also witnesses feasibility on every input.
implements : (f : A → B) (R : B ← A) → Set
implements f R = graph f ⊆ R

-- Local choices for each branch of a nondeterministic algebra suffice to
-- calculate a deterministic implementation for its entire relational fold.
refine-fold : (E : B → Set) (F : B ← (A × B)) (e : B) (s : A → B → B) →
              E e → (∀ a b → F (s a b) (a , b)) →
              implements ⦅ e ∣ s ⦆ (Fold E F)
refine-fold E F e s base step {a = []} refl = nil base
refine-fold E F e s base step {a = x ∷ xs} refl =
  cons (step x _) (refine-fold E F e s base step {a = xs} refl)

-- Specification: choose any subsequence. The relation allows both skipping
-- and keeping; neither maximality nor uniqueness is required.
data Choice {A : Set} : List A ← (A × List A) where
  skip : ∀ {a ys} → Choice ys (a , ys)
  keep : ∀ {a ys} → Choice (a ∷ ys) (a , ys)

open import Agda.Builtin.Bool

module Filter {A : Set} (p : A → Bool) where
  step : A → List A → List A
  step x ys with p x
  ... | true = x ∷ ys
  ... | false = ys

  allowed : ∀ x ys → Choice (step x ys) (x , ys)
  allowed x ys with p x
  ... | true = keep
  ... | false = skip

  filter-correct : implements ⦅ [] ∣ step ⦆ (Fold (_≡ []) Choice)
  filter-correct = refine-fold (_≡ []) Choice [] step refl allowed
