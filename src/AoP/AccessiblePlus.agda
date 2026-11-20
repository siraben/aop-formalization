{-# OPTIONS --safe --without-K #-}
module AoP.AccessiblePlus where

open import AoP.Relations using (_←_; _⊆_; _∘_)
open import AoP.Prelude using (_,_)
open import AoP.Inductive using (Acc; acc)

-- §6.5. A nonempty path takes one predecessor step, followed by
-- zero or more others. Unlike reflexive closure this adds no empty
-- self-step: induction on a nonempty path always has a first edge.
module Law {A : Set} (R : A ← A) where
  data Plus : A ← A where
    one : ∀ {a b} → R b a → Plus b a
    more : ∀ {a b c} → R b a → Plus c b → Plus c a

  least : ∀ (X : A ← A) → R ⊆ X → (X ∘ R) ⊆ X → Plus ⊆ X
  least X start next (one r) = start r
  least X start next (more r rest) = next (_ , least X start next rest , r)

  descend : ∀ {a b} → Acc Plus a → Plus b a → Acc Plus b
  descend (acc smaller) path = smaller _ path
  -- Induction on accessibility supplies accessibility for Plus at
  -- the first child. Its own induction hypotheses cover the rest.
  extend : ∀ {a} → Acc R a → Acc Plus a
  extend (acc smaller) = acc λ { b (one r) → extend (smaller b r)
                             ; b (more r rest) → descend (extend (smaller _ r)) rest }

  restrict : ∀ {a} → Acc Plus a → Acc R a
  restrict (acc smaller) = acc λ b r → restrict (smaller b (one r))
