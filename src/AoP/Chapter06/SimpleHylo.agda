{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SimpleHylo where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter06.Hylo using (module Lists)
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 6.10 for cons-list hylomorphisms. At an input, a producer
-- can stop or emit, never both. When it emits, the label and residual
-- input are unique. The consumer likewise has at most one result at
-- each constructor. Compare two successful runs; neither totality nor
-- termination on unsuccessful inputs is required.
module Law {A B C : Set} (Stop : A → Set) (Emit : (C × A) ← A)
           (Base : B → Set) (Step : B ← (C × B))
           (disjoint : ∀ {a ca} → Stop a → Emit ca a → ⊥)
           (output : ∀ {a p q} → Emit p a → Emit q a → p ≡ q)
           (base : ∀ {b d} → Base b → Base d → b ≡ d)
           (step : ∀ {p b d} → Step b p → Step d p → b ≡ d) where
  open Lists Stop Emit Base Step

  producer : ∀ {a xs ys} → Unfold xs a → Unfold ys a → xs ≡ ys
  producer (done _) (done _) = refl
  producer (done z) (more e _) with disjoint z e
  ... | ()
  producer (more e _) (done z) with disjoint z e
  ... | ()
  producer (more e p) (more f q) with output e f
  ... | refl = cong (_ ∷_) (producer p q)

  consumer : ∀ {xs b d} → Fold Base Step b xs → Fold Base Step d xs → b ≡ d
  consumer (nil e) (nil f) = base e f
  consumer (cons e p) (cons f q) with consumer p q
  ... | refl = step e f

  simple : ∀ {a b d} → Hylo b a → Hylo d a → b ≡ d
  simple (xs , f , p) (ys , g , q) with producer p q
  ... | refl = consumer f g
