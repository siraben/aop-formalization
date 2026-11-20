{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.TabulationMediator where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_; _˘)
open import AoP.Chapter04.Shunting using (graph)

-- Proposition 4.2 in Rel, for any supplied table, regardless of its
-- row representation. A row's two columns determine it uniquely.
module Table {A B T : Set} (R : B ← A) (f : T → B) (g : T → A)
  (find : R ⊆ graph f ∘ graph g ˘) (read : graph f ∘ graph g ˘ ⊆ R)
  (joint : ∀ t u → f t ≡ f u → g t ≡ g u → t ≡ u) where
  module Span {D : Set} (h : D → B) (k : D → A) where
    record Mediator : Set where
      field row : D → T
            target : ∀ d → f (row d) ≡ h d
            source : ∀ d → g (row d) ≡ k d
    open Mediator
    -- Use the same d to form a path between its two observed values.
    -- Inclusion makes that path an R edge; find returns the required row.
    factor : graph h ∘ graph k ˘ ⊆ R → Mediator
    row (factor incl) d = fst (find (incl (d , refl , refl)))
    target (factor incl) d = fst (snd (find (incl (d , refl , refl))))
    source (factor incl) d = snd (snd (find (incl (d , refl , refl))))
    include : Mediator → graph h ∘ graph k ˘ ⊆ R
    include m (d , refl , refl) = read (row m d , target m d , source m d)
    private
      back : ∀ {X : Set} {a b : X} → a ≡ b → b ≡ a
      back refl = refl
    unique : ∀ m n d → row m d ≡ row n d
    unique m n d = joint _ _ (target m d ∙ back (target n d)) (source m d ∙ back (source n d))
