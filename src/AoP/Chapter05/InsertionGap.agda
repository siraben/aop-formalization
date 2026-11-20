{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.InsertionGap where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter05.Permutations using (Insert; front; later)

-- Exercises 5.28 and 6.30. Converse concatenation chooses a gap
-- xs = prefix ++ suffix. Put the new element at the front of the
-- suffix and concatenate again. These two equations characterize
-- exactly the insertion relation, including gaps at either endpoint.
module Law {A : Set} where
  Gap : A → List A → List A → Set
  Gap a xs ys = Σ (List A) λ prefix → Σ (List A) λ suffix →
    (xs ≡ prefix ++ suffix) × (ys ≡ prefix ++ (a ∷ suffix))

  split : ∀ {a xs ys} → Insert a xs ys → Gap a xs ys
  split (front {xs}) = [] , xs , refl , refl
  split (later {x} i) with split i
  ... | pre , suf , eq , placed = (x ∷ pre) , suf , cong (x ∷_) eq , cong (x ∷_) placed

  at-gap : ∀ (a : A) pre suf → Insert a (pre ++ suf) (pre ++ (a ∷ suf))
  at-gap a [] suf = front
  at-gap a (x ∷ pre) suf = later (at-gap a pre suf)
  join : ∀ {a xs ys} → Gap a xs ys → Insert a xs ys
  join {a} (pre , suf , refl , refl) = at-gap a pre suf
