{-# OPTIONS --safe --without-K #-}
module AoP.ReachableDistribution where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)

-- Exercise 7.35, for one container shape with positions P. Given a
-- subproblem at each position, S specifies its feasible answers.
-- Only tuples feasible for this same input ever need to be compared.
module Law {P I A : Set} (S : A ← I) (R : A ← A) (f : (P → A) → A) where
  Feasible : (P → I) → (P → A) → Set
  Feasible input answers = ∀ p → S (answers p) (input p)

  Outputs : (P → I) → A → Set
  Outputs input a = Σ (P → A) λ xs → Feasible input xs × (f xs ≡ a)

  Local = ∀ input xs ys → Feasible input xs → Feasible input ys →
          (∀ p → R (xs p) (ys p)) → R (f xs) (f ys)

  distribute : Local → ∀ input xs → (∀ p → Min R (xs p) (λ a → S a (input p))) →
               Min R (f xs) (Outputs input)
  distribute local input xs winners = (xs , feasible , refl) , lower
    where feasible : Feasible input xs
          feasible p = fst (winners p)
          lower : ∀ a → Outputs input a → R (f xs) a
          lower _ (ys , ok , refl) = local input xs ys feasible ok λ p → snd (winners p) (ys p) (ok p)
