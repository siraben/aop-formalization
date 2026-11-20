{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.OrderedMerge where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; compare)
open import AoP.Chapter06.Selection using (Lower; empty; below; weaken)
open import AoP.Chapter06.SelectionSort using (Sorted; nil; cons)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 6.28 uses a merge at each fork. A trace says which input
-- contributed each occurrence. At a tie either head is legal; the
-- executable comparison takes the left one. Empty lists need no tests.
data Merge : List Nat → List Nat → List Nat → Set where
  exhaustedˡ : ∀ ys → Merge [] ys ys
  exhaustedʳ : ∀ xs → Merge xs [] xs
  left : ∀ {x xs y ys zs} → x ≤ y → Merge xs (y ∷ ys) zs → Merge (x ∷ xs) (y ∷ ys) (x ∷ zs)
  right : ∀ {x xs y ys zs} → y ≤ x → Merge (x ∷ xs) ys zs → Merge (x ∷ xs) (y ∷ ys) (y ∷ zs)

merge : ∀ xs ys → Σ _ (Merge xs ys)
merge [] ys = ys , exhaustedˡ ys
merge (x ∷ xs) ys = walk ys
  where
  walk : ∀ ys → Σ _ (Merge (x ∷ xs) ys)
  walk [] = _ , exhaustedʳ _
  walk (y ∷ ys) with compare x y
  ... | inl xy with merge xs (y ∷ ys)
  ...   | zs , m = _ , left xy m
  walk (y ∷ ys) | inr yx with walk ys
  ...   | zs , m = _ , right yx m

bound : ∀ {a xs ys zs} → Merge xs ys zs → Lower a xs → Lower a ys → Lower a zs
bound (exhaustedˡ _) _ b = b
bound (exhaustedʳ _) a _ = a
bound (left _ m) (below ax a) b = below ax (bound m a b)
bound (right _ m) a (below ay b) = below ay (bound m a b)

ordered : ∀ {xs ys zs} → Merge xs ys zs → Sorted xs → Sorted ys → Sorted zs
ordered (exhaustedˡ _) _ sy = sy
ordered (exhaustedʳ _) sx _ = sx
ordered (left xy m) (cons lx sx) (cons ly sy) =
  cons (bound m lx (below xy (weaken xy ly))) (ordered m sx (cons ly sy))
ordered (right yx m) (cons lx sx) (cons ly sy) =
  cons (bound m (below yx (weaken yx lx)) ly) (ordered m (cons lx sx) sy)

example : fst (merge (1 ∷ 4 ∷ []) (2 ∷ 4 ∷ [])) ≡ 1 ∷ 2 ∷ 4 ∷ 4 ∷ []
example = refl
