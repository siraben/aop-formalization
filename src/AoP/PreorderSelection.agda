{-# OPTIONS --safe --without-K #-}
module AoP.PreorderSelection where

open import AoP.Prelude
open import AoP.Permutations using (Perm; Insert; insert; empty; front; later)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Subsequences using (_∈_; here; there)

-- §6.6. Selecting a least element needs a connected comparison, not
-- antisymmetry: distinct keys may tie. Carry each key unchanged into
-- the selected pair so occurrence preservation is independent of ties.
module Law {A : Set} (R : A → A → Set)
           (trans : ∀ {x y z} → R x y → R y z → R x z)
           (compare : ∀ x y → R x y ⊎ R y x) where
  Bound : A → List A → Set
  Bound a xs = ∀ {b} → b ∈ xs → R a b
  record Result (xs : List A) : Set where
    constructor chose
    field key : A
          rest : List A
          permutation : Perm xs (key ∷ rest)
          lower : Bound key rest

  select : ∀ a xs → Result (a ∷ xs)
  select a [] = chose a [] (insert empty front) (λ ())
  select a (b ∷ bs) with select b bs
  ... | chose k rs p bound with compare a k
  ...   | inl le = chose a (k ∷ rs) (insert p front) λ where
    here → le
    (there i) → trans le (bound i)
  ...   | inr ge = chose k (a ∷ rs) (insert p (later front)) λ where
    here → ge
    (there i) → bound i
