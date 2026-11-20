{-# OPTIONS --safe --without-K #-}
module AoP.CartesianMenuPairs where

open import AoP.Prelude
open import AoP.Power using (_≐_)
open import AoP.ListStrength using (cpr; cpl)
open import AoP.SetifyCombination using (pairing)
open import AoP.Subsequences using (_∈_; image; preimage)
open import AoP.ListProduct using (locate; collect)
open import AoP.Horner using (map)
open import AoP.Naturality using (concat)

-- §5.6. For each left value enumerate one row of pairs, then flatten
-- the rows. Positions may repeat in either menu; membership asks only
-- whether a pair occurs, without requiring equality tests on the values.
module Menus {A B : Set} where
  row : A → List B → List (A × B)
  row a bs = cpr (a , bs)
  cpp : List A → List B → List (A × B)
  cpp as bs = concat (map (λ a → row a bs) as)
  pairs : ∀ as bs → (_∈ cpp as bs) ≐ (λ p → (fst p ∈ as) × (snd p ∈ bs))
  fst (pairs as bs) (a , b) p with locate (λ x → row x bs) as p
  ... | x , present , inside with fst (pairing x bs) (a , b) inside
  ...   | refl , q = present , q
  snd (pairs as bs) (a , b) (p , q) = collect (λ x → row x bs) p (snd (pairing a bs) (a , b) (refl , q))
  -- Holding the right value fixed leaves only the left menu to scan.
  column : ∀ (as : List A) (b : B) → (_∈ cpl (as , b)) ≐ (λ p → (fst p ∈ as) × (snd p ≡ b))
  fst (column as b) p h with preimage (λ a → a , b) as h
  ... | a , found , refl = found , refl
  snd (column as b) (a , .b) (p , refl) = image (λ x → x , b) p
