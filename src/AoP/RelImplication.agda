{-# OPTIONS --safe --without-K #-}
module AoP.RelImplication where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Polynomial using (_⊎_; inl; inr)
private variable A B : Set

-- An edge of R ⇒ S explains how to turn an R-edge at the same pair
-- of endpoints into an S-edge. The universal property moves an R
-- assumption between the input intersection and the output implication.
infixr 5 _⇒_ _∪_
_⇒_ _∪_ : (B ← A) → (B ← A) → B ← A
(R ⇒ S) b a = R b a → S b a
(R ∪ S) b a = R b a ⊎ S b a

intro : {R S T : B ← A} → (T ⊓ R ⊆ S) → T ⊆ R ⇒ S
intro law t r = law (t , r)
elim : {R S T : B ← A} → (T ⊆ R ⇒ S) → T ⊓ R ⊆ S
elim law (t , r) = law t r

-- Exercise 4.32. Each pair of inclusions is an equality of relations.
module Laws (R S T : B ← A) where
  unpack : R ⇒ (S ⇒ T) ⊆ (R ⊓ S) ⇒ T
  unpack = intro {R = R ⊓ S} {S = T} {T = R ⇒ (S ⇒ T)} λ { (h , (r , s)) → h r s }
  pack : (R ⊓ S) ⇒ T ⊆ R ⇒ (S ⇒ T)
  pack = intro {R = R} {S = S ⇒ T} {T = (R ⊓ S) ⇒ T} λ { (h , r) s → h (r , s) }

  split-input : (R ∪ S) ⇒ T ⊆ (R ⇒ T) ⊓ (S ⇒ T)
  split-input h = (λ r → h (inl r)) , (λ s → h (inr s))
  join-input : (R ⇒ T) ⊓ (S ⇒ T) ⊆ (R ∪ S) ⇒ T
  join-input = intro {R = R ∪ S} {S = T} {T = (R ⇒ T) ⊓ (S ⇒ T)} λ { ((f , g) , inl r) → f r ; ((f , g) , inr s) → g s }

  split-output : R ⇒ (S ⊓ T) ⊆ (R ⇒ S) ⊓ (R ⇒ T)
  split-output h = (λ r → fst (h r)) , (λ r → snd (h r))
  join-output : (R ⇒ S) ⊓ (R ⇒ T) ⊆ R ⇒ (S ⊓ T)
  join-output = intro {R = R} {S = S ⊓ T} {T = (R ⇒ S) ⊓ (R ⇒ T)} λ { ((f , g) , r) → f r , g r }

  apply : R ⊓ (R ⇒ S) ⊆ R ⊓ S
  apply (r , h) = r , h r
  keep : R ⊓ S ⊆ R ⊓ (R ⇒ S)
  keep (r , s) = r , λ _ → s
