{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.ScriptRelationInduction where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_)
open import AoP.Chapter04.Shunting using (graph)

-- Point-free induction rule for relations out of lists. Equalities
-- about particular scripts can be confined to the constructor cases:
-- precompose both sides with each constructor graph, then cancel that
-- case distinction once at the outer inclusion.
module Law {A B : Set} (L H : B ← List A) where
  Empty : List A ← ⊤
  Empty = graph (λ _ → [])
  Push : A → List A ← List A
  Push x = graph (x ∷_)

  Local : List A → Set
  Local xs = ∀ {b} → L b xs → H b xs

  derive : L ∘ Empty ⊆ H ∘ Empty →
           (∀ x xs → Local xs → ∀ {b} → (L ∘ Push x) b xs → (H ∘ Push x) b xs) → L ⊆ H
  derive base step {a = []} p with base {a = tt} ([] , p , refl)
  ... | .[] , result , refl = result
  derive base step {a = x ∷ xs} p with step x xs (derive base step {a = xs}) ((x ∷ xs) , p , refl)
  ... | .(x ∷ xs) , result , refl = result
