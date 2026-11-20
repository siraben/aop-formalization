{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.Inductive where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter06.Hylo using (module Lists)
open import AoP.Chapter02.Polynomial using (inl; inr)

-- §6.5. Accessibility gives an induction hypothesis for *every* recursive
-- call permitted by a decomposition, not just the call one program picks.
data Acc {A : Set} (R : A ← A) (a : A) : Set where
  acc : (∀ b → R b a → Acc R b) → Acc R a

module Unique {A B C : Set} (Stop : A → Set) (Emit : (C × A) ← A)
              (Base : B → Set) (Step : B ← (C × B)) where
  open Lists Stop Emit Base Step

  Child : A ← A
  Child a′ a = Σ C λ c → Emit (c , a′) a

  -- Leastness already bounds Hylo by any prefixpoint. To get the
  -- opposite inclusion, unfold the proposed solution and descend in Acc.
  greatest-at : (X : B ← A) → X ⊆ Φ X → ∀ {a b} → Acc Child a → X b a → Hylo b a
  greatest-at X un (acc smaller) x with un x
  ... | inl z = fold (inl z)
  ... | inr (c , a′ , b′ , emit , x′ , step) =
    fold (inr (c , a′ , b′ , emit , greatest-at X un (smaller a′ (c , emit)) x′ , step))

  unique : (∀ a → Acc Child a) → (X : B ← A) → Φ X ⊆ X → X ⊆ Φ X →
           (Hylo ⊆ X) × (X ⊆ Hylo)
  unique wf X closed un = least X closed , λ { {b} {a} x → greatest-at X un (wf a) x }
