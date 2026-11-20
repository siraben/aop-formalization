{-# OPTIONS --safe --without-K #-}
module AoP.PartitionPredicate where

open import AoP.Prelude
open import AoP.Paragraph using (_∷⁺_)
open import AoP.PartitionRanges using (module Law)
open import AoP.PartitionFlatten using () renaming (module Law to Enumeration)
open import AoP.Power using (ℙ)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Subsequences using (_∈_)

-- Exercise 5.27. Compute the predicate of valid partitions directly.
-- Each step takes the union of two images of the previous predicate:
-- start a singleton block, or extend a first block that already exists.
-- No list of every partition is needed to describe the output set.
module Build (A : Set) where
  open Law A
  open Enumeration A using (partitions; sound′; recover)
  step : A → ℙ Parts → ℙ Parts
  step w P bs = (Σ Parts λ ps → P ps × (new (w , ps) ≡ bs)) ⊎
                (Σ Parts λ ps → P ps × Glue bs (w , ps))
  pred : List A → ℙ Parts
  pred [] bs = bs ≡ []
  pred (w ∷ ws) = step w (pred ws)

  open import AoP.Paragraph using (module Layout)
  open Layout {Word = A} (λ _ → 0) 0 using (flatten)
  exact : ∀ ws bs → pred ws bs → flatten bs ≡ ws
  exact [] .[] refl = refl
  exact (w ∷ ws) ._ (inl (ps , p , refl)) = cong (w ∷_) (exact ws ps p)
  exact (w ∷ ws) ._ (inr (._ , p , glue .w b bs)) = cong (w ∷_) (exact ws (b ∷ bs) p)

  all : ∀ bs → pred (flatten bs) bs
  all [] = refl
  all ((w ∷⁺ xs) ∷ bs) = first w xs bs (all bs)
    where
    first : ∀ w xs bs → pred (flatten bs) bs → pred (flatten ((w ∷⁺ xs) ∷ bs)) ((w ∷⁺ xs) ∷ bs)
    first w [] bs p = inl (bs , p , refl)
    first w (v ∷ vs) bs p = inr (_ , first v vs bs p , glue w (v ∷⁺ vs) bs)

  listed : ∀ ws bs → pred ws bs → bs ∈ partitions ws
  listed ws bs p = recover ws bs (exact ws bs p)
  admitted : ∀ ws bs → bs ∈ partitions ws → pred ws bs
  admitted ws bs p = transport (sound′ ws bs p) (all bs)
    where transport : ∀ {x y} → x ≡ y → pred x bs → pred y bs
          transport refl proof = proof
