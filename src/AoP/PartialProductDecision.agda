{-# OPTIONS --safe --without-K #-}
module AoP.PartialProductDecision where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.PartialGraphCategory using (Partial; partial; module Partial)
open import AoP.PartialProduct using (BothOrOne; onlyL; onlyR; both)
open import AoP.Relations using (_∘_)

-- §2.5. Why does the executable pack use Maybe? With arbitrary partial
-- graphs a three-way tagged product would let us decide definedness.
-- Test it on a left leg always returning unit and a right leg whose only
-- possible output is unit, available exactly when a chosen type P holds.
Tags = BothOrOne ⊤ ⊤

data L : ⊤ → Tags → Set where
  alone : L tt (onlyL tt)
  shared : L tt (both tt tt)
data R : ⊤ → Tags → Set where
  alone : R tt (onlyR tt)
  shared : R tt (both tt tt)

module Test (P : Set) where
  right : Partial ⊤ ⊤
  right = partial (λ _ _ → P) (λ _ _ → refl)

  -- Only existence of a pairing and its projection equations are used.
  -- Totality on the left supplies a concrete tag. A shared tag certifies
  -- P; a left-only tag precludes P by uniqueness of the pairing output.
  decide : (m : Partial ⊤ Tags) → (L ∘ Partial.edge m) tt tt →
           (P → (R ∘ Partial.edge m) tt tt) → ((R ∘ Partial.edge m) tt tt → P) → P ⊎ (P → ⊥)
  decide m (_ , (L.shared , e)) give read = inl (read (_ , (R.shared , e)))
  decide m (_ , (L.alone , e)) give read = inr refute
    where
    disjoint : ∀ {t} → onlyL tt ≡ t → R tt t → ⊥
    disjoint refl ()
    refute : P → ⊥
    refute p with give p
    ... | t , (r , h) = disjoint (Partial.single m e h) r
