{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.SubsequenceLayerCalculation where

open import AoP.Common.Prelude
open import AoP.Chapter04.Power using (ℙ; _≐_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter05.Refinement using (Choice; keep; skip)
open import AoP.Chapter05.ListFoldByMembership using (module Calculate)
open import AoP.Chapter05.Subsequences using (_∈_; subs; merge; split; image; preimage)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (_++_)

-- §5.6. Transpose the keep-or-skip step *before* choosing how sets
-- are represented. A keep edge contributes to the image under cons;
-- a skip edge contributes an unchanged tail. The union need not be
-- disjoint: the executable list may enumerate a result twice.
module Derive {A : Set} where
  module C = Calculate {A} {List A} (_≡ []) Choice
  keep-or-skip : ∀ a (P : ℙ (List A)) → C.extend a P ≐
    (λ ys → (Σ _ λ zs → P zs × ((a ∷ zs) ≡ ys)) ⊎ P ys)
  fst (keep-or-skip a P) _ (zs , p , keep) = inl (zs , p , refl)
  fst (keep-or-skip a P) _ (zs , p , skip) = inr p
  snd (keep-or-skip a P) _ (inl (zs , p , refl)) = zs , p , keep
  snd (keep-or-skip a P) ys (inr p) = ys , p , skip

  -- Represent the tail predicate by membership in a finite list. Map
  -- realizes image, append realizes union; this calculation works for
  -- any candidate accumulator, not only one produced by subs.
  update : ∀ a (pool : List (List A)) → C.extend a (_∈ pool) ≐ ( _∈ (map (a ∷_) pool ++ pool))
  fst (update a pool) ys h with fst (keep-or-skip a _) ys h
  ... | inl (zs , p , refl) = merge _ _ (inl (image (a ∷_) p))
  ... | inr p = merge (map (a ∷_) pool) pool (inr p)
  snd (update a pool) ys p with split (map (a ∷_) pool) pool p
  ... | inr q = ys , q , skip
  ... | inl q with preimage (a ∷_) pool q
  ...   | zs , m , refl = zs , m , keep

  -- Equal values at different positions give two distinct choices.
  -- The membership specification allows the executable fold to keep both.
  repeated : (a : A) → subs (a ∷ a ∷ []) ≡
    (a ∷ a ∷ []) ∷ (a ∷ []) ∷ (a ∷ []) ∷ [] ∷ []
  repeated a = refl
