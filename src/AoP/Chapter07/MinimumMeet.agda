{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MinimumMeet where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.6. For two objectives on the same candidates, a common
-- minimum must attain both lower bounds at the same member of X.
module Meet {A : Set} (R S : A ← A) where
  separate : ∀ {a X} → Min (R ⊓ S) a X → Min R a X × Min S a X
  separate (member , bound) = (member , (λ b x → fst (bound b x))) ,
                               member , (λ b x → snd (bound b x))

  combine : ∀ {a X} → Min R a X × Min S a X → Min (R ⊓ S) a X
  combine ((member , r) , _ , s) = member , λ b x → r b x , s b x

-- Exercise 7.13. Intersect a preorder with equality of observations
-- under f. This is comparison within fibres; composing two witnesses
-- composes their order comparisons and their observation equalities.
module Fibre {A B : Set} (R : A ← A) (f : A → B) where
  Within : A ← A
  Within a b = R a b × (f a ≡ f b)

  reflexive : (∀ a → R a a) → ∀ a → Within a a
  reflexive rr a = rr a , refl

  transitive : R ∘ R ⊆ R → Within ∘ Within ⊆ Within
  transitive tr (b , (r , eq) , s , eq′) = tr (b , r , s) , (eq ∙ eq′)
