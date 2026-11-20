{-# OPTIONS --safe --without-K #-}
module AoP.ProjectedLoop where

open import AoP.Prelude
open import AoP.Naturality using (_++_)

-- Exercise 10.1. The reference loop accumulates both a materialized
-- output prefix and the current column. The transformed loop needs
-- only the column to compute the next chunk and emits it immediately.
module Law {A B C : Set} (emit : C → A → List B) (advance : C → A → C) where
  loop : List B × C → List A → List B × C
  loop s [] = s
  loop (ys , c) (x ∷ xs) = loop (ys ++ emit c x , advance c x) xs

  stream : C → List A → List B
  stream c [] = []
  stream c (x ∷ xs) = emit c x ++ stream (advance c x) xs

  private
    unit : ∀ (ys : List B) → ys ≡ ys ++ []
    unit [] = refl
    unit (y ∷ ys) = cong (y ∷_) (unit ys)
    assoc : ∀ (us vs ws : List B) → (us ++ vs) ++ ws ≡ us ++ (vs ++ ws)
    assoc [] vs ws = refl
    assoc (u ∷ us) vs ws = cong (u ∷_) (assoc us vs ws)

  invariant : ∀ ys c xs → fst (loop (ys , c) xs) ≡ ys ++ stream c xs
  invariant ys c [] = unit ys
  invariant ys c (x ∷ xs) = begin
    fst (loop (ys ++ emit c x , advance c x) xs)
      ≡⟨ invariant (ys ++ emit c x) (advance c x) xs ⟩
    (ys ++ emit c x) ++ stream (advance c x) xs
      ≡⟨ assoc ys (emit c x) (stream (advance c x) xs) ⟩
    ys ++ stream c (x ∷ xs) ∎

  project : ∀ c xs → fst (loop ([] , c) xs) ≡ stream c xs
  project c xs = invariant [] c xs
