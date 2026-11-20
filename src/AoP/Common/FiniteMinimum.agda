{-# OPTIONS --safe --without-K #-}
module AoP.Common.FiniteMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Common.NatOrder using (_≤_; rid; chain; compare)
open import Agda.Builtin.Nat using (Nat)

-- A finite search may be empty or entirely infeasible. Rather than use
-- an artificial infinite score, return either an optimal witness or a
-- proof ruling out *every* candidate. This scanner will select layouts
-- by waste after enumeration, discarding lines which exceed the margin.
module Search {A : Set} (P : A → Set) (test : ∀ x → P x ⊎ (P x → ⊥)) (cost : A → Nat) where
  data Result (xs : List A) : Set where
    none : (∀ x → x ∈ xs → P x → ⊥) → Result xs
    best : (x : A) → x ∈ xs → P x →
           (∀ y → y ∈ xs → P y → cost x ≤ cost y) → Result xs

  absurd : ∀ {X : Set} → ⊥ → X
  absurd ()

  scan : ∀ xs → Result xs
  scan [] = none (λ _ ())
  scan (x ∷ xs) with test x | scan xs
  ... | inr reject | none no = none λ where
    _ here p → reject p
    y (there m) p → no y m p
  ... | inl px | none no = best x here px λ where
    _ here _ → rid _
    y (there m) py → absurd (no y m py)
  ... | inr reject | best y m py opt = best y (there m) py λ where
    _ here p → absurd (reject p)
    z (there n) p → opt z n p
  ... | inl px | best y m py opt with compare (cost x) (cost y)
  ...   | inl le = best x here px λ where
    _ here _ → rid _
    z (there n) p → chain le (opt z n p)
  ...   | inr ge = best y (there m) py λ where
    _ here _ → ge
    z (there n) p → opt z n p
