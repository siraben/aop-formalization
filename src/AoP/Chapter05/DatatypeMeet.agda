{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.DatatypeMeet where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊓_; _⊆_)

-- Exercise 5.18. At an initial datatype, its relation lifting is the
-- unique homomorphism satisfying the constructor equation. Write that
-- equation after exposing the outer constructor of each endpoint. This
-- pins both uses of the layer law to the *same* two layers: there is
-- no need to distribute intersection over relational composition.
module Derive (F : Set → Set → Set) (T : Set → Set)
  (out : ∀ {A} → T A → F A (T A))
  (layer : ∀ {A B X Y} → B ← A → Y ← X → F B Y ← F A X)
  (lift : ∀ {A B} → B ← A → T B ← T A) where

  Step : ∀ {A B} → B ← A → T B ← T A → T B ← T A
  Step R H v u = layer R H (out v) (out u)
  Equation : ∀ {A B} → B ← A → T B ← T A → Set
  Equation R H = (H ⊆ Step R H) × (Step R H ⊆ H)

  module At {A B : Set} (R S : B ← A)
    (computeR : Equation R (lift R)) (computeS : Equation S (lift S))
    (split : ∀ {X Y} (H K : Y ← X) → layer (R ⊓ S) (H ⊓ K) ⊆ layer R H ⊓ layer S K)
    (join : ∀ {X Y} (H K : Y ← X) → layer R H ⊓ layer S K ⊆ layer (R ⊓ S) (H ⊓ K))
    (unique : ∀ H → Equation (R ⊓ S) H → (H ⊆ lift (R ⊓ S)) × (lift (R ⊓ S) ⊆ H)) where

    -- Candidate homomorphism: meet the lifted relations. Unfold its
    -- components separately, then combine them by the layer meet law.
    candidate : Equation (R ⊓ S) (lift R ⊓ lift S)
    fst candidate (r , s) = join (lift R) (lift S) (fst computeR r , fst computeS s)
    snd candidate edge with split (lift R) (lift S) edge
    ... | r , s = snd computeR r , snd computeS s

    meet : (lift (R ⊓ S) ⊆ lift R ⊓ lift S) × (lift R ⊓ lift S ⊆ lift (R ⊓ S))
    meet with unique (lift R ⊓ lift S) candidate
    ... | into , from = from , into
