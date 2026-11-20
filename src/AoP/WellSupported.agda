{-# OPTIONS --safe --without-K #-}
module AoP.WellSupported where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)
open import AoP.MinimalComparison using (Test)
open import AoP.WellBounded using (Bounded)
open import AoP.StrictBoundCounterexample using (Equal; not-bounded)

-- Exercises 7.30–7.31. A minimum is minimal, so a witness of
-- well-boundedness supplies a witness of well-supportedness.
Supported : ∀ {A} → (A ← A) → Set₁
Supported {A} R = ∀ (X : A → Set) a → X a → Σ A λ b → Min (Test R) b X

weaken : ∀ {A} {R : A ← A} → Bounded R → Supported R
weaken wb X a xa with wb X a xa
... | b , xb , least = b , xb , λ c xc _ → least c xc

-- Boolean equality, already proved not-bounded, is well-supported:
-- for any inhabited set simply take the supplied member.
equality-supported : Supported Equal
equality-supported X a xa = a , xa , λ { _ _ refl → refl }

-- To find a minimal element below a particular member a, restrict the
-- search to its predecessors in X. Transitivity puts any challenger
-- of the returned element inside that same restricted search set.
module Cover {A : Set} (R : A ← A) (rr : ∀ a → R a a)
             (tr : ∀ {a b c} → R a b → R b c → R a c) (support : Supported R) where
  below : ∀ (X : A → Set) a → X a → Σ A λ b → R b a × Min (Test R) b X
  below X a xa with support (λ c → X c × R c a) a (xa , rr a)
  ... | b , (xb , ba) , minimal = b , ba , xb , λ c xc cb → minimal c (xc , tr cb ba) cb
