{-# OPTIONS --safe --without-K #-}
module AoP.FibrePowerThinning where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _⊓_; _∘_; _˘)
open import AoP.Thinning using (Pred; Min; Thin; thin; min-after-thin)
open import AoP.PowerRelator using (Lift)

-- 8.11: P(min R ∘ Λ S₁) permits distinct choices among tied
-- minima. Forward coverage of the power relator supplies a minimum
-- for the *same* intermediate state as each rival; backward coverage
-- explains why every selected candidate is actually attainable.
module Law {I B : Set} (S₁ : B ← I) (Q R : B ← B)
  (safe : R ⊓ (S₁ ∘ S₁ ˘) ⊆ Q) where
  M : B ← I
  M b i = Min R b (λ x → S₁ x i)
  Reach : Pred I → Pred B
  Reach enabled b = Σ I λ i → enabled i × S₁ b i
  local : ∀ {enabled kept} → Lift M kept enabled → Thin Q kept (Reach enabled)
  Thin.subset (local choices) k with Lift.backward choices _ k
  ... | i , on , feasible , least = i , on , feasible
  Thin.cover (local choices) b (i , on , rival) with Lift.forward choices i on
  ... | a , kept , feasible , least = a , kept , safe (least b rival , i , feasible , rival)
  minimum : Q ⊆ R → (∀ {a b c} → R a b → R b c → R a c) →
    ∀ {enabled kept a} → Lift M kept enabled → Min R a kept → Min R a (Reach enabled)
  minimum sub trans choices = min-after-thin sub trans (local choices)
